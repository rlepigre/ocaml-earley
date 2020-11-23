(* Copyright 2016-2020 Christophe Raffalli & Rodolphe Lepigre. *)

open Parser_spec_ast
open Asttypes
open Parsetree
open Ast_helper
open Extra

type str_item = Parsetree.structure_item
type expr = Parsetree.expression

let locate =
  let find_locate () =
    try Some(Exp.ident {txt = Lident(Sys.getenv "LOCATE"); loc = Location.none})
    with Not_found -> None
  in
  Lazy.from_fun find_locate

let mk_fun loc args e =
  let args = List.map (fun s -> Pat.var (Location.mknoloc s)) args in
  List.fold_right (Exp.fun_ ~loc Nolabel None) args e

let mk_app loc e args =
  Exp.apply ~loc e (List.map (fun e -> (Nolabel, e)) args)

let mk_lid s = Location.mknoloc (Longident.parse s)
let mk_id s = Exp.ident (mk_lid s)

let mk_appv loc e args =
  let fn s = (Nolabel, Exp.ident (Location.mknoloc (Longident.parse s))) in
  Exp.apply ~loc e (List.map fn args)

let core_apply loc fn args =
  let fn = Location.mknoloc (Longident.parse ("Earley_core.Earley." ^ fn)) in
  Exp.apply ~loc (Exp.ident fn) (List.map (fun e -> (Nolabel, e)) args)

let regexp_apply loc nameo e1 e2 =
  let fn = Location.mknoloc (Longident.parse "Earley_str.regexp") in
  let name = match nameo with None -> [] | Some e -> [(Labelled "name", e)] in
  Exp.apply ~loc (Exp.ident fn) (name @ [(Nolabel, e1); (Nolabel, e2)])

let new_regexp_apply loc nameo e1 =
  let fn = Location.mknoloc (Longident.parse "Earley_core.Earley.regexp") in
  let name = match nameo with None -> [] | Some e -> [(Labelled "name", e)] in
  Exp.apply ~loc (Exp.ident fn) (name @ [(Nolabel, e1)])

let mk_constr loc id arg =
  Exp.construct ~loc (Location.mknoloc (Longident.parse id)) arg

let mk_unit loc = mk_constr loc "()" None

let or_unit loc eo = match eo with Some(e) -> e | None -> mk_unit loc

let mk_nil loc = mk_constr loc "[]" None
let mk_cons loc e1 e2 = mk_app loc (mk_id "List.cons") [e1; e2]

(** [occurs_in_expr id e] tests whether identifier (i.e.,  free variable) [id]
    occurs in the expression [e]. *)
let occurs_in_expr : string -> expr -> bool = fun id e ->
  let open Ast_iterator in
  let open Parsetree in
  let rec expr iter e =
    match e.pexp_desc with
    | Pexp_ident({txt = Lident(x)}) when x = id -> raise Exit
    | _                                         ->
        default_iterator.expr {default_iterator with expr} e
  in
  try expr {default_iterator with expr} e; false with Exit -> true

let rec occurs_in_action : string -> parser_action -> bool = fun id action ->
  match action with
  | Ppact_default   -> false
  | Ppact_action(e) -> occurs_in_expr id e
  | Ppact_dseq(r)   -> ignore r; true (* TODO *)

let build_re loc e opt =
  let act =
    let zero = Exp.constant ~loc (Const.int 0) in
    mk_fun loc ["group"]
      (Option.default (mk_app loc (mk_id "group") [zero]) opt)
  in
  let name =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident id } ->
        let id =
          let l = String.length id in
          if l > 3 && String.sub id (l - 3) 3 = "_re" then
            String.sub id 0 (l - 3)
          else id
        in
        Some (Exp.constant (Const.string id))
    | _                              -> None
  in
  regexp_apply loc name e act

let build_re_litteral loc s opt =
  let opt =
    let zero = Exp.constant ~loc (Const.int 0) in
    Option.default (mk_app loc (mk_id "group") [zero]) opt
  in
  let es = String.escaped s in
  let act = mk_fun loc ["group"] opt in
  regexp_apply loc (Some (Exp.constant (Const.string es)))
    (Exp.constant (Const.string s)) act

let build_new_re_litteral loc s opt =
  let es = String.escaped s in
  let s = "\\(" ^ s ^ "\\)" in
  let re =
    new_regexp_apply loc (Some (Exp.constant (Const.string es)))
      (Exp.constant (Const.string s))
  in
  match opt with
  | None   -> re
  | Some e -> core_apply loc "apply" [mk_fun loc ["group"] e; re]

let build_parser_element_atom loc uid ov oe =
  match (uid.txt, ov, oe) with
  | ("EOF"  , None   , _      ) ->
      (oe = None, core_apply loc "eof" [or_unit loc oe])
  | ("EMPTY", None   , _      ) ->
      (oe = None, core_apply loc "empty" [or_unit loc oe])
  | ("FAIL" , None   , None   ) ->
      (true, core_apply loc "fail" [mk_unit loc])
  | ("DEBUG", Some(e), None   ) ->
      (true, core_apply loc "debug" [e])
  | ("CHR"  , Some(e), _      ) ->
      (oe = None, core_apply loc "char" [e; Option.default e oe])
  | ("STR"  , Some(e), _      ) ->
      (oe = None, core_apply loc "string" [e; Option.default e oe])
  | ("ANY"  , None   , None   ) ->
      (false, mk_id "Earley_core.Earley.any")
  | ("BLANK", None   , _      ) ->
      (oe = None, core_apply loc "with_blank_test" [or_unit loc oe])
  | ("RE"   , Some(e), _      ) ->
      (false, build_re loc e oe)
  | (uid    , _      , _      ) ->
      failwith ("Invalid parser atom " ^ uid ^ ".")

type full_parser_element = {
  fpe_loc: Location.t;
  (** Source code location for the whole parser element. *)
  fpe_expr: expr;
  (** Expression generated for the parser combinator. *)
  fpe_is_bound: bool;
  (** Should the parsed value be bound? *)
  fpe_toplevel_id: string Location.loc option;
  (** Bound pattern identifier for the whole result in the action. *)
  fpe_pattern: patt option;
  (** Rest of the pattern to be bound in the action. *)
  fpe_modifier: (parser_modifier * expr option) option;
  (** Possible parser modifier. *)
  fpe_greedy: bool;
  (** Is the element marked as being greedy. *)
}

type full_parser_rule = {
  fpr_loc: Location.t;
  (** Source code location for the whole parser rule. *)
  fpr_wrapper: expr -> expr;
  (** A wrapper for the generated expression (typically used for lets). *)
  fpr_lhs: (full_parser_element * bool) list;
  (** Elements forming the rule, bool [true] means result used in action. *)
  fpr_guard: expr option;
  (** Optional rule guard (controls when the rule applies). *)
  fpr_action: parser_action;
  (** The semantic action of the rule. *)
  fpr_uses_main_loc: bool;
  (** Is the location of the full rule used in the action? *)
}

let rec parser_element : parser_element -> full_parser_element = fun pe ->
  let loc = pe.ppelt_loc in
  let (boring, e) =
    match pe.ppelt_desc with
    | Ppelt_atom(uid,ov,oe) ->
        build_parser_element_atom loc uid ov oe
    | Ppelt_char(c,oe)      ->
        let e = Exp.constant ~loc (Const.char c) in
        (oe = None, core_apply loc "char" [e; Option.default e oe])
    | Ppelt_string(s,oe)    ->
        let e = Exp.constant ~loc (Const.string s) in
        (oe = None, core_apply loc "string" [e; Option.default e oe])
    | Ppelt_regexp(s,b,oe)  ->
        let build = if b then build_new_re_litteral else build_re_litteral in
        (false, build loc s oe)
    | Ppelt_expr(e)         ->
        (false, e)
    | Ppelt_grammar(g)      ->
        (false, parser_grammar g)
    | Ppelt_noblank(oe)     ->
        (oe = None, core_apply loc "no_blank_test" [or_unit loc oe])
  in
  let (fpe_is_bound, fpe_toplevel_id, fpe_pattern) =
    match pe.ppelt_pat with
    | None             -> let is_bound =
                             pe.ppelt_modifier <> None || not boring
                          in
                          (is_bound, None    , None   )
    | Some(p)          ->
    match p.ppat_desc with
    | Ppat_alias(p,id) -> (true    , Some(id), Some(p))
    | Ppat_var(id)     -> (true    , Some(id), None   )
    | Ppat_any         -> (false   , None    , None   )
    | _                -> (true    , None    , Some(p))
  in
  {fpe_loc = loc; fpe_expr = e; fpe_is_bound; fpe_toplevel_id; fpe_pattern;
  fpe_modifier = pe.ppelt_modifier; fpe_greedy = pe.ppelt_greedy}

and parser_rule : parser_rule -> full_parser_rule = fun r ->
  let (fpr_lhs, _) =
    let fn elt (acc, i) =
      let elt = parser_element elt in
      if elt.fpe_toplevel_id = None && elt.fpe_is_bound then
        let id = Location.mknoloc (Printf.sprintf "_default_%i" i) in
        (({elt with fpe_toplevel_id = Some(id)}, false) :: acc, i + 1)
      else
        let occur =
          match elt.fpe_toplevel_id with
          | None     -> false
          | Some(id) -> occurs_in_action ("_loc_" ^ id.txt) r.pprule_action
        in
        ((elt, occur) :: acc, i)
    in
    List.fold_right fn r.pprule_pelts ([], 0)
  in
  let fpr_uses_main_loc = occurs_in_action "_loc" r.pprule_action in
  {fpr_loc = r.pprule_loc; fpr_wrapper = r.pprule_wrapper; fpr_lhs;
  fpr_guard = r.pprule_guard; fpr_action = r.pprule_action; fpr_uses_main_loc}

and parser_grammar : parser_grammar -> expr = fun gram ->
  build_alternative gram.ppgram_loc None gram

and build_action loc occur_loc ids e =
  let mkpatt loc (id, p) =
    match (id, p) with
    | (Some(id), Some(p)) -> Pat.alias ~loc p id
    | (Some(id), None   ) -> Pat.var ~loc id
    | (None    , Some(p)) -> p
    | (None    , None   ) -> assert false (* Unreachable. *)
  in
  let e =
    let fn e ((id, x), visible) =
      match (Lazy.force locate, visible) with
      | (Some(f), true) ->
          let id = match id with Some(id) -> id | None -> assert false in
          let args = ["str1"; "pos1"; "str2"; "pos2"] in
          let pat_loc_id = Pat.var (Location.mknoloc ("_loc_" ^ id.txt)) in
          let vb = Vb.mk pat_loc_id (mk_appv loc f args) in
          let e = Exp.let_ Nonrecursive [vb] e in
          mk_fun loc args (Exp.fun_ ~loc Nolabel None (mkpatt loc (Some id,x)) e)
      | (_      , _   ) ->
          if id = None && x = None then e else
          Exp.fun_ ~loc Nolabel None (mkpatt loc (id,x)) e
    in
    List.fold_left fn e (List.rev ids)
  in
  match (Lazy.force locate, occur_loc) with
  | (Some(locate), true) ->
      let args =
        [ "__loc__start__buf" ; "__loc__start__pos"
        ; "__loc__end__buf"   ; "__loc__end__pos"   ]
      in
      let vb = Vb.mk (Pat.var (Location.mknoloc "_loc")) (mk_appv loc locate args) in
      mk_fun loc args (Exp.let_ Nonrecursive [vb] e)
  | (_           , _   ) -> e

and apply_option loc (opt : (parser_modifier * expression option) option) (g : bool) e =
  let fn e f d =
    match d with
    | None   ->
        let f_some =
          let x_exp = Exp.ident (Location.mknoloc (Longident.parse "x")) in
          mk_fun loc ["x"] (mk_constr loc "Some" (Some x_exp))
        in
        let e = core_apply loc "apply" [f_some; e] in
        core_apply loc f [mk_constr loc "None" None; e]
    | Some d ->
        core_apply loc f [d; e]
  in
  let gn e f d =
    match d with
    | None   ->
        let f_app_nil =
          mk_fun loc ["f"] (mk_app loc (mk_id "f") [mk_constr loc "[]" None])
        in
        let arg2 =
          let id = mk_fun loc ["l"] (mk_id "l") in
          let fn =
            mk_fun loc ["x"; "f"; "l"] (
              mk_app loc (mk_id "f") [mk_cons loc (mk_id "x") (mk_id "l")])
          in
          core_apply loc (f ^ "'") [id; e; fn]
        in
        core_apply loc "apply" [f_app_nil; arg2]
    | Some d ->
        core_apply loc f [d; e]
  in
  let kn e g = if g then core_apply loc "greedy" [e] else e in
  match opt with
  | None                  -> kn e g
  | Some((Ppmod_opt , d)) -> kn (fn e "option" d) g
  | Some((Ppmod_star, d)) -> kn (gn e "fixpoint" d) g
  | Some((Ppmod_plus, d)) -> kn (gn e "fixpoint1" d) g


and default_action loc (l : full_parser_element list) =
  let p x = x.fpe_toplevel_id <> None || x.fpe_is_bound in
  let f x =
    match x.fpe_toplevel_id  with
    | Some(id) -> Exp.ident ~loc:id.loc (mk_lid id.txt)
    | None     -> assert false
  in
  match List.map f (List.filter p l) with
  | []  -> mk_unit loc
  | [e] -> e
  | l   -> Exp.tuple ~loc l

and build_rule r =
  let _loc = r.pprule_loc in
  let l =
    let fn elt (acc, i) =
      let elt = parser_element elt in
      if elt.fpe_toplevel_id = None && elt.fpe_is_bound then
        let id = Location.mknoloc (Printf.sprintf "_default_%i" i) in
        ({elt with fpe_toplevel_id = Some(id)} :: acc, i + 1)
      else
        (elt :: acc, i)
    in
    fst (List.fold_right fn r.pprule_pelts ([], 0))
  in
  let (iter, action) =
    match r.pprule_action with
    | Ppact_default   -> (false, default_action _loc l)
    | Ppact_action(a) -> (false, a)
    | Ppact_dseq(r)   ->
        let (def, cond, a) = build_rule r in
        true, (match cond with
              | None -> def a
              | Some cond ->
                 def (Exp.ifthenelse ~loc:_loc cond a (Some (core_apply
                 _loc "fail" [mk_unit _loc]))))
  in
  let occur_loc = occurs_in_expr "_loc" action in
  let action_is_id id =
    match (action.pexp_desc, id) with
    | (Pexp_ident({txt = Lident(x)}), Some(y)) -> x = y.txt
    | (_                            , _      ) -> false
  in
  let rec fn ids elts =
    match elts with
    | []                                                  ->
        let f =
          match (Lazy.force locate, occur_loc) with
          | (Some(_), true) -> "empty_pos"
          | (_      , _   ) -> "empty"
        in
        core_apply _loc f [build_action _loc occur_loc ids action]
    | [elt] when ids = [] && action_is_id elt.fpe_toplevel_id ->
        apply_option elt.fpe_loc elt.fpe_modifier elt.fpe_greedy elt.fpe_expr
    | elt :: elts                                           ->
        let e =
          apply_option elt.fpe_loc elt.fpe_modifier elt.fpe_greedy
            elt.fpe_expr
        in
        let occur_loc_id =
          match elt.fpe_toplevel_id with
          | None     -> false
          | Some(id) -> occurs_in_expr ("_loc_" ^ id.txt) action
        in
        let id = (elt.fpe_toplevel_id, elt.fpe_pattern) in
        let a = fn ((id, occur_loc_id) :: ids) elts in
        let fn =
          match (Lazy.force locate, occur_loc_id) with
          | (Some _, true)                         -> "fsequence_position"
          | _ when fst id = None && snd id = None  -> "fsequence_ignore"
          | _                                      -> "fsequence"
        in
        core_apply _loc fn [e; a]
  in
  let res = fn [] l in
  let res = if iter then core_apply _loc "iter" [res] else res in
  (r.pprule_wrapper, r.pprule_guard, res)

and apply_def_cond _loc r =
  let (def,cond,e) = build_rule r in
  match cond with
    None -> def e
  | Some c ->
    def (Exp.ifthenelse ~loc:_loc c e (Some (core_apply _loc "fail" [mk_unit _loc])))

and apply_def_cond_list loc r acc =
  let (def,cond,e) = build_rule r in
  match cond with
  | None   -> def (mk_cons loc e acc)
  | Some c -> def (mk_app loc (mk_id "List.append")
                     [Exp.ifthenelse ~loc c (mk_cons loc e (mk_constr loc
                     "[]" None))  (Some (mk_constr loc "[]" None)); acc])

and apply_def_cond_prio loc arg r acc =
  let (def,cond,e) = build_rule r in
  match cond with
  | None   -> def (mk_cons loc (Exp.tuple [Exp.fun_ Nolabel None (Pat.any ()) (mk_constr loc "true" None); e]) acc)
  | Some c -> def (mk_cons loc (Exp.tuple [Exp.fun_ Nolabel None arg c; e]) acc)

and build_alternative loc prio gram =
  let build_alternative loc ls =
    (* FIXME: warning if useless @| ? *)
    match List.map snd ls with
    | []  -> core_apply loc "fail" [mk_unit loc]
    | [r] -> apply_def_cond loc r
    | rs  ->
    let l = List.fold_right (apply_def_cond_list loc) rs (mk_nil loc) in
    core_apply loc "alternatives" [l]
  in
  let build_prio_alternative loc prio ls =
    let l0, l1 = List.partition fst ls in
    let l0 = List.map snd l0 and l1 = List.map snd l1 in
    let l1 = List.fold_right (apply_def_cond_prio loc prio) l1 (mk_nil loc) in
    let l0 = List.fold_right (apply_def_cond_list loc) l0 (mk_nil loc) in
    Exp.tuple ~loc [l1; Exp.fun_ Nolabel None prio l0]
  in
  match prio with
  | None       -> build_alternative loc gram.ppgram_rules
  | Some(prio) -> build_prio_alternative loc prio gram.ppgram_rules



let build_str_items loc l =
  let rec build bs =
    match bs with
    | []      -> ([], [], [])
    | b :: bs ->
    let (str1, str2, str3) = build bs in
    match b.ppbind_desc with
    | Ppbind_ocaml(vb)  -> (str1, str2, vb :: str3)
    | Ppbind_parser(pb) ->
    let name = pb.ppspec_name.txt in
    let args = pb.ppspec_args in
    let prio = pb.ppspec_prio in
    let ty = pb.ppspec_type in
    let loc_r = pb.ppspec_gram.ppgram_loc in
    let r = pb.ppspec_gram in
    let pname = Pat.var ~loc:pb.ppspec_name.loc (Location.mknoloc name) in
    let coer f =
      match ty with
      | None    -> f
      | Some ty -> Exp.constraint_ ~loc f ty
    in
    let args_pat =
      match args with
      | []  -> Pat.construct ~loc (mk_lid "()") None
      | [p] -> p
      | _   -> Pat.tuple ~loc args
    in
    let (str1, str2) =
      match args,prio with
      | [], None ->
         let r = coer (build_alternative loc_r prio r) in
         let s1 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc pname
               (core_apply loc "declare_grammar"
                 [Exp.constant (Const.string name)])]
         in
         let s2 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc (Pat.any ~loc ())
               (core_apply loc "set_grammar" [mk_id name; r])]
         in
         (s1 :: str1, s2 :: str2)
      | _, None ->
         let r = coer (build_alternative loc_r prio r) in
         let set_name = name ^ "__set__grammar" in
         let s1 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc
               (Pat.tuple [pname; Pat.var (Location.mknoloc set_name)])
               (core_apply loc "grammar_family"
                 [Exp.constant (Const.string name)])]
         in
         let s2 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc (Pat.any ~loc ())
               (mk_app loc (mk_id set_name)
                 [Exp.fun_ ~loc Nolabel None args_pat r])]
         in
         (s1 :: str1, s2 :: str2)
      | [], Some _ ->
         let r = coer (build_alternative loc_r prio r) in
         let set_name = name ^ "__set__grammar" in
         let s1 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc
               (Pat.tuple [pname; Pat.var (Location.mknoloc set_name)])
               (core_apply loc "grammar_prio"
                 [Exp.constant (Const.string name)])]
         in
         let s2 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc (Pat.any ~loc ())
               (mk_app loc (mk_id set_name) [r])]
         in
         (s1 :: str1, s2 :: str2)
      | args, Some _ ->
         let r = coer (build_alternative loc_r prio r) in
         let set_name = name ^ "__set__grammar" in
         let s1 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc
               (Pat.tuple [pname; Pat.var (Location.mknoloc set_name)])
               (core_apply loc "grammar_prio_family"
                 [Exp.constant (Const.string name)])]
         in
         let s2 =
           Str.value ~loc Nonrecursive
             [Vb.mk ~loc (Pat.any ~loc ())
               (mk_app loc (mk_id set_name)
                 [Exp.fun_ ~loc Nolabel None args_pat r])]
         in
         (s1 :: str1, s2 :: str2)
    in
    let str2 =
      match args, prio with
      | ([], _) | ([_], None) -> str2
      | _ ->
        let rec currify acc n = function
          | []   ->
            begin
              let acc = List.rev acc in
              match prio with
              | None   -> mk_app loc (mk_id name) [Exp.tuple acc]
              | Some _ -> mk_fun loc ["__curry__prio"] (
                            mk_app loc (mk_id name)
                              [Exp.tuple acc; mk_id "__curry__prio"]
                          )
            end
          | a::l ->
             let v = "__curry__varx"^string_of_int n in
             let acc = mk_id v :: acc in
             mk_fun loc [v] (currify acc (n+1) l)
        in
        let f = currify [] 0 args in
        (Str.value ~loc Nonrecursive [Vb.mk ~loc pname f]) :: str2
    in
    (str1, str2, str3)
  in
  let (str1, str2, str3) = build l in
  let str3 = if str3 = [] then [] else [Str.value ~loc Recursive str3] in
  str1 @ str3 @ str2

let parser_bindings : parser_bindings -> str_item list = fun bs ->
  build_str_items bs.ppbinds_loc bs.ppbinds_desc

let parser_expr : parser_expr -> expr = fun pe ->
  let args = pe.ppexpr_args in
  let e = build_alternative pe.ppexpr_loc pe.ppexpr_prio pe.ppexpr_gram in
  List.fold_right (Exp.fun_ ~loc:pe.ppexpr_loc Nolabel None) args e
