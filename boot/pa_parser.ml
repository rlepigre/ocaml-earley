open Earley_core
open Asttypes
open Parsetree
open Longident
open Location
open Pa_ocaml_prelude
open Pa_lexing
open Ast_helper
type action =
  | Default 
  | Normal of expression 
  | DepSeq of ((expression -> expression) * expression option * expression) 
let occurs_in_expr id e =
  let open Ast_iterator in
    let rec expr iter e =
      match e.pexp_desc with
      | Pexp_ident { txt = Lident x } when x = id -> raise Exit
      | _ -> default_iterator.expr { default_iterator with expr } e in
    try expr { default_iterator with expr } e; false with | Exit -> true
let occur id act =
  match act with
  | Default -> false
  | Normal e|DepSeq (_, None, e) -> occurs_in_expr id e
  | DepSeq (_, Some e1, e2) ->
      (occurs_in_expr id e1) || (occurs_in_expr id e2)
let find_locate () =
  try
    Some
      (Exp.ident
         { txt = (Lident (Sys.getenv "LOCATE")); loc = Location.none })
  with | Not_found -> None
let mkpatt loc (id, p) =
  let id = mkloc id loc in
  match p with | None -> Pat.var ~loc id | Some p -> Pat.alias ~loc p id
let mk_fun loc args e =
  let args = List.map (fun s -> Pat.var (mknoloc s)) args in
  List.fold_right (Exp.fun_ ~loc Nolabel None) args e
let mk_app loc e args =
  Exp.apply ~loc e (List.map (fun e -> (Nolabel, e)) args)
let mk_lid s = mknoloc (Longident.parse s)
let mk_id s = Exp.ident (mk_lid s)
let mk_appv loc e args =
  let fn s = (Nolabel, (Exp.ident (mknoloc (Longident.parse s)))) in
  Exp.apply ~loc e (List.map fn args)
let core_apply loc fn args =
  let fn = mknoloc (Longident.parse ("Earley_core.Earley." ^ fn)) in
  Exp.apply ~loc (Exp.ident fn) (List.map (fun e -> (Nolabel, e)) args)
let regexp_apply loc nameo e1 e2 =
  let fn = mknoloc (Longident.parse "Earley_str.regexp") in
  let name =
    match nameo with | None -> [] | Some e -> [((Labelled "name"), e)] in
  Exp.apply ~loc (Exp.ident fn) (name @ [(Nolabel, e1); (Nolabel, e2)])
let new_regexp_apply loc nameo e1 =
  let fn = mknoloc (Longident.parse "Earley_core.Earley.regexp") in
  let name =
    match nameo with | None -> [] | Some e -> [((Labelled "name"), e)] in
  Exp.apply ~loc (Exp.ident fn) (name @ [(Nolabel, e1)])
let mk_constr loc id arg =
  Exp.construct ~loc (mknoloc (Longident.parse id)) arg
let mk_unit loc = mk_constr loc "()" None
let or_unit loc eo = match eo with | Some e -> e | None -> mk_unit loc
let mk_cons loc e1 e2 = mk_app loc (mk_id "List.cons") [e1; e2]
let rec build_action loc occur_loc ids e =
  let e =
    let fn e ((id, x), visible) =
      match ((find_locate ()), visible) with
      | (Some f, true) ->
          let args = ["str1"; "pos1"; "str2"; "pos2"] in
          let pat_loc_id = Pat.var (mknoloc ("_loc_" ^ id)) in
          let vb = Vb.mk pat_loc_id (mk_appv loc f args) in
          let e = Exp.let_ Nonrecursive [vb] e in
          mk_fun loc args (Exp.fun_ ~loc Nolabel None (mkpatt loc (id, x)) e)
      | (_, _) ->
          if (id = "_") && (x = None)
          then e
          else Exp.fun_ ~loc Nolabel None (mkpatt loc (id, x)) e in
    List.fold_left fn e (List.rev ids) in
  match ((find_locate ()), occur_loc) with
  | (Some locate, true) ->
      let args =
        ["__loc__start__buf";
        "__loc__start__pos";
        "__loc__end__buf";
        "__loc__end__pos"] in
      let vb = Vb.mk (Pat.var (mknoloc "_loc")) (mk_appv loc locate args) in
      mk_fun loc args (Exp.let_ Nonrecursive [vb] e)
  | (_, _) -> e
let apply_option loc opt e =
  let fn e f d =
    match d with
    | None ->
        let f_some =
          let x_exp = Exp.ident (mknoloc (Longident.parse "x")) in
          mk_fun loc ["x"] (mk_constr loc "Some" (Some x_exp)) in
        let e = core_apply loc "apply" [f_some; e] in
        core_apply loc f [mk_constr loc "None" None; e]
    | Some d -> core_apply loc f [d; e] in
  let gn e f d =
    match d with
    | None ->
        let f_app_nil =
          mk_fun loc ["f"] (mk_app loc (mk_id "f") [mk_constr loc "[]" None]) in
        let arg2 =
          let id = mk_fun loc ["l"] (mk_id "l") in
          let fn =
            mk_fun loc ["x"; "f"; "l"]
              (mk_app loc (mk_id "f") [mk_cons loc (mk_id "x") (mk_id "l")]) in
          core_apply loc (f ^ "'") [id; e; fn] in
        core_apply loc "apply" [f_app_nil; arg2]
    | Some d -> core_apply loc f [d; e] in
  let kn e = function | None -> e | Some _ -> core_apply loc "greedy" [e] in
  match opt with
  | `Once -> e
  | `Option (d, g) -> kn (fn e "option" d) g
  | `Greedy -> core_apply loc "greedy" [e]
  | `Fixpoint (d, g) -> kn (gn e "fixpoint" d) g
  | `Fixpoint1 (d, g) -> kn (gn e "fixpoint1" d) g
let default_action loc l =
  let p x =
    match x with | `Normal (("_", _), false, _, _, _) -> false | _ -> true in
  let f x =
    match x with
    | `Normal ((id, _), _, _, _, _) -> Exp.ident ~loc (mk_lid id)
    | _ -> assert false in
  match List.map f (List.filter p l) with
  | [] -> mk_unit loc
  | e::[] -> e
  | l -> Exp.tuple ~loc l
let from_opt ov d = match ov with | None -> d | Some v -> v
let dash =
  let fn str pos =
    let (c, str', pos') = Input.read str pos in
    if c = '-'
    then
      let (c', _, _) = Input.read str' pos' in
      (if c' = '>' then Earley.give_up () else ((), str', pos'))
    else Earley.give_up () in
  Earley.black_box fn (Charset.singleton '-') false "-"
let expr_arg = expression_lvl (NoMatch, (next_exp App))
let build_rule (_loc, occur_loc, def, l, condition, action) =
  let (iter, action) =
    match action with
    | Normal a -> (false, a)
    | Default -> (false, (default_action _loc l))
    | DepSeq (def, cond, a) ->
        (true,
          ((match cond with
            | None -> def a
            | Some cond ->
                def
                  (Exp.ifthenelse ~loc:_loc cond a
                     (Some (core_apply _loc "fail" [mk_unit _loc])))))) in
  let rec fn ids l =
    match l with
    | [] ->
        let a = build_action _loc occur_loc ids action in
        let f =
          match ((find_locate ()), occur_loc) with
          | (Some _, true) -> "empty_pos"
          | _ -> "empty" in
        core_apply _loc f [a]
    | (`Normal (id, _, e, opt, occur_loc_id))::[] when
        match action.pexp_desc with
        | Pexp_ident { txt = Lident id' } when (ids = []) && ((fst id) = id')
            -> true
        | _ -> false ->
        (assert (not occur_loc);
         assert (not occur_loc_id);
         apply_option _loc opt e)
    | (`Normal (id, _, e, opt, occur_loc_id))::ls ->
        let e = apply_option _loc opt e in
        let a = fn ((id, occur_loc_id) :: ids) ls in
        let fn =
          match ((find_locate ()), occur_loc_id) with
          | (Some _, true) -> "fsequence_position"
          | _ when ((fst id) = "_") && ((snd id) = None) ->
              "fsequence_ignore"
          | _ -> "fsequence" in
        core_apply _loc fn [e; a] in
  let res = fn [] l in
  let res = if iter then core_apply _loc "iter" [res] else res in
  (def, condition, res)
let apply_def_cond _loc r =
  let (def, cond, e) = build_rule r in
  match cond with
  | None -> def e
  | Some c ->
      def
        (Exp.ifthenelse ~loc:_loc c e
           (Some (core_apply _loc "fail" [mk_unit _loc])))
let apply_def_cond_list loc r acc =
  let (def, cond, e) = build_rule r in
  match cond with
  | None -> def (mk_cons loc e acc)
  | Some c ->
      def
        (mk_app loc (mk_id "List.append")
           [Exp.ifthenelse ~loc c (mk_cons loc e (mk_constr loc "[]" None))
              (Some (mk_constr loc "[]" None));
           acc])
let apply_def_cond_prio loc arg r acc =
  let (def, cond, e) = build_rule r in
  match cond with
  | None ->
      def
        (mk_cons loc
           (Exp.tuple
              [Exp.fun_ Nolabel None (Pat.any ()) (mk_constr loc "true" None);
              e]) acc)
  | Some c ->
      def (mk_cons loc (Exp.tuple [Exp.fun_ Nolabel None arg c; e]) acc)
let build_alternatives loc ls =
  let ls = List.map snd ls in
  match ls with
  | [] -> core_apply loc "fail" [mk_unit loc]
  | r::[] -> apply_def_cond loc r
  | _::_::_ ->
      let l =
        List.fold_right (apply_def_cond_list loc) ls
          (mk_constr loc "[]" None) in
      core_apply loc "alternatives" [l]
let build_prio_alternatives loc arg ls =
  let (l0, l1) = List.partition fst ls in
  let l0 = List.map snd l0
  and l1 = List.map snd l1 in
  let l1 =
    List.fold_right (apply_def_cond_prio loc arg) l1
      (mk_constr loc "[]" None) in
  let l0 =
    List.fold_right (apply_def_cond_list loc) l0 (mk_constr loc "[]" None) in
  Exp.tuple ~loc [l1; Exp.fun_ Nolabel None arg l0]
let build_str_item _loc l =
  let rec fn =
    function
    | [] -> ([], [], [])
    | (`Caml b)::l ->
        let (str1, str2, str3) = fn l in (str1, str2, (b :: str3))
    | (`Parser (name, args, prio, ty, _loc_r, r))::l ->
        let (str1, str2, str3) = fn l in
        let pname = Pat.var ~loc:_loc (mknoloc name) in
        let coer f =
          match ty with
          | None -> f
          | Some ty -> Exp.constraint_ ~loc:_loc f ty in
        let args_pat =
          match args with
          | [] -> Pat.construct ~loc:_loc (mk_lid "()") None
          | p::[] -> p
          | _ -> Pat.tuple ~loc:_loc args in
        let (str1, str2) =
          match (args, prio) with
          | ([], None) ->
              let r = coer (build_alternatives _loc_r r) in
              let s1 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc pname
                     (core_apply _loc "declare_grammar"
                        [Exp.constant (Const.string name)])] in
              let s2 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc (Pat.any ~loc:_loc ())
                     (core_apply _loc "set_grammar" [mk_id name; r])] in
              ((s1 :: str1), (s2 :: str2))
          | (_, None) ->
              let r = coer (build_alternatives _loc_r r) in
              let set_name = name ^ "__set__grammar" in
              let s1 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc
                     (Pat.tuple [pname; Pat.var (mknoloc set_name)])
                     (core_apply _loc "grammar_family"
                        [Exp.constant (Const.string name)])] in
              let s2 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc (Pat.any ~loc:_loc ())
                     (mk_app _loc (mk_id set_name)
                        [Exp.fun_ ~loc:_loc Nolabel None args_pat r])] in
              ((s1 :: str1), (s2 :: str2))
          | ([], Some prio) ->
              let r = coer (build_prio_alternatives _loc_r prio r) in
              let set_name = name ^ "__set__grammar" in
              let s1 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc
                     (Pat.tuple [pname; Pat.var (mknoloc set_name)])
                     (core_apply _loc "grammar_prio"
                        [Exp.constant (Const.string name)])] in
              let s2 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc (Pat.any ~loc:_loc ())
                     (mk_app _loc (mk_id set_name) [r])] in
              ((s1 :: str1), (s2 :: str2))
          | (args, Some prio) ->
              let r = coer (build_prio_alternatives _loc_r prio r) in
              let set_name = name ^ "__set__grammar" in
              let s1 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc
                     (Pat.tuple [pname; Pat.var (mknoloc set_name)])
                     (core_apply _loc "grammar_prio_family"
                        [Exp.constant (Const.string name)])] in
              let s2 =
                Str.value ~loc:_loc Nonrecursive
                  [Vb.mk ~loc:_loc (Pat.any ~loc:_loc ())
                     (mk_app _loc (mk_id set_name)
                        [Exp.fun_ ~loc:_loc Nolabel None args_pat r])] in
              ((s1 :: str1), (s2 :: str2)) in
        let str2 =
          match (args, prio) with
          | ([], _)|(_::[], None) -> str2
          | _ ->
              let rec currify acc n =
                function
                | [] ->
                    let acc = List.rev acc in
                    (match prio with
                     | None -> mk_app _loc (mk_id name) [Exp.tuple acc]
                     | Some _ ->
                         mk_fun _loc ["__curry__prio"]
                           (mk_app _loc (mk_id name)
                              [Exp.tuple acc; mk_id "__curry__prio"]))
                | a::l ->
                    let v = "__curry__varx" ^ (string_of_int n) in
                    let acc = (mk_id v) :: acc in
                    mk_fun _loc [v] (currify acc (n + 1) l) in
              let f = currify [] 0 args in
              (Str.value ~loc:_loc Nonrecursive [Vb.mk ~loc:_loc pname f]) ::
                str2 in
        (str1, str2, str3) in
  let (str1, str2, str3) = fn l in
  if str3 = []
  then str1 @ str2
  else str1 @ ((Str.value ~loc:_loc Recursive str3) :: str2)
let build_re loc e opt =
  let act =
    mk_fun loc ["group"]
      (from_opt opt (mk_app loc (mk_id "group") [Exp.constant (Const.int 0)])) in
  let name =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident id } ->
        let id =
          let l = String.length id in
          if (l > 3) && ((String.sub id (l - 3) 3) = "_re")
          then String.sub id 0 (l - 3)
          else id in
        Some (Exp.constant (Const.string id))
    | _ -> None in
  regexp_apply loc name e act
let build_re_litteral loc s opt =
  let opt =
    from_opt opt (mk_app loc (mk_id "group") [Exp.constant (Const.int 0)]) in
  let es = String.escaped s in
  let act = mk_fun loc ["group"] opt in
  regexp_apply loc (Some (Exp.constant (Const.string es)))
    (Exp.constant (Const.string s)) act
let build_new_re_litteral loc s opt =
  let es = String.escaped s in
  let s = "\\(" ^ (s ^ "\\)") in
  let re =
    new_regexp_apply loc (Some (Exp.constant (Const.string es)))
      (Exp.constant (Const.string s)) in
  match opt with
  | None -> re
  | Some e -> core_apply loc "apply" [mk_fun loc ["group"] e; re]
let parser_atom = Earley_core.Earley.declare_grammar "parser_atom"
let parser_param = Earley_core.Earley.declare_grammar "parser_param"
let parser_modifier = Earley_core.Earley.declare_grammar "parser_modifier"
let glr_ident = Earley_core.Earley.declare_grammar "glr_ident"
let glr_left_member = Earley_core.Earley.declare_grammar "glr_left_member"
let glr_let = Earley_core.Earley.declare_grammar "glr_let"
let glr_cond = Earley_core.Earley.declare_grammar "glr_cond"
let (glr_action, glr_action__set__grammar) =
  Earley_core.Earley.grammar_family "glr_action"
let (glr_rule, glr_rule__set__grammar) =
  Earley_core.Earley.grammar_family "glr_rule"
let (glr_at_rule, glr_at_rule__set__grammar) =
  Earley_core.Earley.grammar_family "glr_at_rule"
let glr_rules = Earley_core.Earley.declare_grammar "glr_rules"
let _ =
  Earley_core.Earley.set_grammar parser_atom
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence dash
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.option None
                   (Earley_core.Earley.apply (fun x -> Some x) parser_param))
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun oe ->
                              fun _default_0 ->
                                ((oe = None),
                                  (core_apply _loc "no_blank_test"
                                     [or_unit _loc oe]))))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "EOF" "EOF")
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.option None
                      (Earley_core.Earley.apply (fun x -> Some x)
                         parser_param))
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun oe ->
                                 ((oe = None),
                                   (core_apply _loc "eof" [or_unit _loc oe]))))))
             (List.cons
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "EMPTY" "EMPTY")
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x)
                            parser_param))
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun oe ->
                                    ((oe = None),
                                      (core_apply _loc "empty"
                                         [or_unit _loc oe]))))))
                (List.cons
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.string "FAIL" "FAIL")
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  (true,
                                    (core_apply _loc "fail" [mk_unit _loc])))))
                   (List.cons
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.string "DEBUG" "DEBUG")
                         (Earley_core.Earley.fsequence expr_arg
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun e ->
                                          (true,
                                            (core_apply _loc "debug" [e]))))))
                      (List.cons
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.string "CHR" "CHR")
                            (Earley_core.Earley.fsequence expr_arg
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.option None
                                     (Earley_core.Earley.apply
                                        (fun x -> Some x) parser_param))
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun oe ->
                                                fun e ->
                                                  ((oe = None),
                                                    (core_apply _loc "char"
                                                       [e; from_opt oe e])))))))
                         (List.cons
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.string "STR" "STR")
                               (Earley_core.Earley.fsequence expr_arg
                                  (Earley_core.Earley.fsequence
                                     (Earley_core.Earley.option None
                                        (Earley_core.Earley.apply
                                           (fun x -> Some x) parser_param))
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun oe ->
                                                   fun e ->
                                                     ((oe = None),
                                                       (core_apply _loc
                                                          "string"
                                                          [e; from_opt oe e])))))))
                            (List.cons
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.string "ANY" "ANY")
                                  (Earley_core.Earley.empty
                                     (false,
                                       (mk_id "Earley_core.Earley.any"))))
                               (List.cons
                                  (Earley_core.Earley.fsequence_ignore
                                     (Earley_core.Earley.string "BLANK"
                                        "BLANK")
                                     (Earley_core.Earley.fsequence
                                        (Earley_core.Earley.option None
                                           (Earley_core.Earley.apply
                                              (fun x -> Some x) parser_param))
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun oe ->
                                                      ((oe = None),
                                                        (core_apply _loc
                                                           "with_blank_test"
                                                           [or_unit _loc oe]))))))
                                  (List.cons
                                     (Earley_core.Earley.fsequence_ignore
                                        (Earley_core.Earley.string "RE" "RE")
                                        (Earley_core.Earley.fsequence
                                           expr_arg
                                           (Earley_core.Earley.fsequence
                                              (Earley_core.Earley.option None
                                                 (Earley_core.Earley.apply
                                                    (fun x -> Some x)
                                                    parser_param))
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun oe ->
                                                            fun e ->
                                                              (false,
                                                                (build_re
                                                                   _loc e oe)))))))
                                     (List.cons
                                        (Earley_core.Earley.fsequence
                                           char_litteral
                                           (Earley_core.Earley.fsequence
                                              (Earley_core.Earley.option None
                                                 (Earley_core.Earley.apply
                                                    (fun x -> Some x)
                                                    parser_param))
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun oe ->
                                                            fun c ->
                                                              let e =
                                                                Exp.constant
                                                                  ~loc:_loc
                                                                  (Const.char
                                                                    c) in
                                                              ((oe = None),
                                                                (core_apply
                                                                   _loc
                                                                   "char"
                                                                   [e;
                                                                   from_opt
                                                                    oe e]))))))
                                        (List.cons
                                           (Earley_core.Earley.fsequence
                                              string_litteral
                                              (Earley_core.Earley.fsequence
                                                 (Earley_core.Earley.option
                                                    None
                                                    (Earley_core.Earley.apply
                                                       (fun x -> Some x)
                                                       parser_param))
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
                                                       fun __loc__start__pos
                                                         ->
                                                         fun __loc__end__buf
                                                           ->
                                                           fun
                                                             __loc__end__pos
                                                             ->
                                                             let _loc =
                                                               locate
                                                                 __loc__start__buf
                                                                 __loc__start__pos
                                                                 __loc__end__buf
                                                                 __loc__end__pos in
                                                             fun oe ->
                                                               fun
                                                                 ((s, _) as
                                                                    _default_0)
                                                                 ->
                                                                 let e =
                                                                   Exp.constant
                                                                    (Const.string
                                                                    s) in
                                                                 ((oe = None),
                                                                   (core_apply
                                                                    _loc
                                                                    "string"
                                                                    [e;
                                                                    from_opt
                                                                    oe e]))))))
                                           (List.cons
                                              (Earley_core.Earley.fsequence
                                                 regexp_litteral
                                                 (Earley_core.Earley.fsequence
                                                    (Earley_core.Earley.option
                                                       None
                                                       (Earley_core.Earley.apply
                                                          (fun x -> Some x)
                                                          parser_param))
                                                    (Earley_core.Earley.empty_pos
                                                       (fun __loc__start__buf
                                                          ->
                                                          fun
                                                            __loc__start__pos
                                                            ->
                                                            fun
                                                              __loc__end__buf
                                                              ->
                                                              fun
                                                                __loc__end__pos
                                                                ->
                                                                let _loc =
                                                                  locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                fun oe ->
                                                                  fun s ->
                                                                    (false,
                                                                    (build_re_litteral
                                                                    _loc s oe))))))
                                              (List.cons
                                                 (Earley_core.Earley.fsequence
                                                    new_regexp_litteral
                                                    (Earley_core.Earley.fsequence
                                                       (Earley_core.Earley.option
                                                          None
                                                          (Earley_core.Earley.apply
                                                             (fun x -> Some x)
                                                             parser_param))
                                                       (Earley_core.Earley.empty_pos
                                                          (fun
                                                             __loc__start__buf
                                                             ->
                                                             fun
                                                               __loc__start__pos
                                                               ->
                                                               fun
                                                                 __loc__end__buf
                                                                 ->
                                                                 fun
                                                                   __loc__end__pos
                                                                   ->
                                                                   let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                   fun oe ->
                                                                    fun s ->
                                                                    (false,
                                                                    (build_new_re_litteral
                                                                    _loc s oe))))))
                                                 (List.cons
                                                    (Earley_core.Earley.fsequence
                                                       value_path
                                                       (Earley_core.Earley.empty_pos
                                                          (fun
                                                             __loc__start__buf
                                                             ->
                                                             fun
                                                               __loc__start__pos
                                                               ->
                                                               fun
                                                                 __loc__end__buf
                                                                 ->
                                                                 fun
                                                                   __loc__end__pos
                                                                   ->
                                                                   let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                   fun id ->
                                                                    (false,
                                                                    (Exp.ident
                                                                    ~loc:_loc
                                                                    (mkloc id
                                                                    _loc))))))
                                                    (List.cons
                                                       (Earley_core.Earley.fsequence_ignore
                                                          (Earley_core.Earley.string
                                                             "(" "(")
                                                          (Earley_core.Earley.fsequence
                                                             expression
                                                             (Earley_core.Earley.fsequence_ignore
                                                                (Earley_core.Earley.string
                                                                   ")" ")")
                                                                (Earley_core.Earley.empty
                                                                   (fun e ->
                                                                    (false,
                                                                    e))))))
                                                       (List.cons
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.char
                                                                '{' '{')
                                                             (Earley_core.Earley.fsequence
                                                                glr_rules
                                                                (Earley_core.Earley.fsequence_ignore
                                                                   (Earley_core.Earley.char
                                                                    '}' '}')
                                                                   (Earley_core.Earley.empty_pos
                                                                    (fun
                                                                    __loc__start__buf
                                                                    ->
                                                                    fun
                                                                    __loc__start__pos
                                                                    ->
                                                                    fun
                                                                    __loc__end__buf
                                                                    ->
                                                                    fun
                                                                    __loc__end__pos
                                                                    ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun r ->
                                                                    (false,
                                                                    (build_alternatives
                                                                    _loc r)))))))
                                                          []))))))))))))))))))
let _ =
  Earley_core.Earley.set_grammar parser_param
    (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '[' '[')
       (Earley_core.Earley.fsequence expression
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char ']' ']')
             (Earley_core.Earley.empty (fun _default_0 -> _default_0)))))
let _ =
  Earley_core.Earley.set_grammar parser_modifier
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty `Once))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '*' '*')
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.option None
                      (Earley_core.Earley.apply (fun x -> Some x)
                         parser_param))
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x)
                            (Earley_core.Earley.char '$' '$')))
                      (Earley_core.Earley.empty
                         (fun g -> fun e -> `Fixpoint (e, g))))))
             (List.cons
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '+' '+')
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x)
                            parser_param))
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.option None
                            (Earley_core.Earley.apply (fun x -> Some x)
                               (Earley_core.Earley.char '$' '$')))
                         (Earley_core.Earley.empty
                            (fun g -> fun e -> `Fixpoint1 (e, g))))))
                (List.cons
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '?' '?')
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.option None
                            (Earley_core.Earley.apply (fun x -> Some x)
                               parser_param))
                         (Earley_core.Earley.fsequence
                            (Earley_core.Earley.option None
                               (Earley_core.Earley.apply (fun x -> Some x)
                                  (Earley_core.Earley.char '$' '$')))
                            (Earley_core.Earley.empty
                               (fun g -> fun e -> `Option (e, g))))))
                   (List.cons
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '$' '$')
                         (Earley_core.Earley.empty `Greedy)) []))))))
let _ =
  Earley_core.Earley.set_grammar glr_ident
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty (None, ("_", None))))
          (List.cons
             (Earley_core.Earley.fsequence (pattern_lvl (true, ConstrPat))
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ':' ':')
                   (Earley_core.Earley.empty
                      (fun p ->
                         match p.ppat_desc with
                         | Ppat_alias (p, { txt = id }) ->
                             ((Some true), (id, (Some p)))
                         | Ppat_var { txt = id } ->
                             ((Some (id <> "_")), (id, None))
                         | Ppat_any -> ((Some false), ("_", None))
                         | _ -> ((Some true), ("_", (Some p))))))) [])))
let _ =
  Earley_core.Earley.set_grammar glr_left_member
    (Earley_core.Earley.apply (fun f -> f [])
       (Earley_core.Earley.fixpoint1' (fun l -> l)
          (Earley_core.Earley.fsequence glr_ident
             (Earley_core.Earley.fsequence parser_atom
                (Earley_core.Earley.fsequence parser_modifier
                   (Earley_core.Earley.empty
                      (fun opt ->
                         fun ((boring, s) as _default_0) ->
                           fun ((cst', id) as _default_1) ->
                             `Normal
                               (id,
                                 (from_opt cst'
                                    ((opt <> `Once) || (not boring))), s,
                                 opt))))))
          (fun x -> fun f -> fun l -> f (List.cons x l))))
let _ =
  Earley_core.Earley.set_grammar glr_let
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty (fun x -> x)))
          (List.cons
             (Earley_core.Earley.fsequence let_kw
                (Earley_core.Earley.fsequence rec_flag
                   (Earley_core.Earley.fsequence let_binding
                      (Earley_core.Earley.fsequence in_kw
                         (Earley_core.Earley.fsequence glr_let
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun l ->
                                          fun _default_0 ->
                                            fun lbs ->
                                              fun r ->
                                                fun _default_1 ->
                                                  fun x ->
                                                    Exp.let_ ~loc:_loc r lbs
                                                      (l x)))))))) [])))
let _ =
  Earley_core.Earley.set_grammar glr_cond
    (Earley_core.Earley.option None
       (Earley_core.Earley.apply (fun x -> Some x)
          (Earley_core.Earley.fsequence_ignore when_kw
             (Earley_core.Earley.fsequence expression
                (Earley_core.Earley.empty (fun e -> e))))))
let _ =
  glr_action__set__grammar
    (fun alm ->
       Earley_core.Earley.alternatives
         (List.cons
            (Earley_core.Earley.fsequence_ignore
               (Earley_core.Earley.empty ())
               (Earley_core.Earley.empty Default))
            (List.cons
               (Earley_core.Earley.fsequence_ignore
                  (Earley_core.Earley.string "->>" "->>")
                  (Earley_core.Earley.fsequence (glr_rule alm)
                     (Earley_core.Earley.empty
                        (fun r -> DepSeq (build_rule r)))))
               (List.cons
                  (Earley_core.Earley.fsequence_ignore
                     (Earley_core.Earley.string "->" "->")
                     (Earley_core.Earley.fsequence
                        (if alm
                         then expression
                         else expression_lvl (Let, Seq))
                        (Earley_core.Earley.fsequence no_semi
                           (Earley_core.Earley.empty
                              (fun _default_0 -> fun a -> Normal a))))) []))))
let _ =
  glr_rule__set__grammar
    (fun alm ->
       Earley_core.Earley.fsequence glr_let
         (Earley_core.Earley.fsequence glr_left_member
            (Earley_core.Earley.fsequence glr_cond
               (Earley_core.Earley.fsequence (glr_action alm)
                  (Earley_core.Earley.empty_pos
                     (fun __loc__start__buf ->
                        fun __loc__start__pos ->
                          fun __loc__end__buf ->
                            fun __loc__end__pos ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              fun action ->
                                fun cond ->
                                  fun l ->
                                    fun def ->
                                      let fn x (res, i) =
                                        match x with
                                        | `Normal (("_", a), true, c, d) ->
                                            (((`Normal
                                                 ((("_default_" ^
                                                      (string_of_int i)), a),
                                                   true, c, d, false)) ::
                                              res), (i + 1))
                                        | `Normal (id, b, c, d) ->
                                            let occur_loc_id =
                                              ((fst id) <> "_") &&
                                                (occur ("_loc_" ^ (fst id))
                                                   action) in
                                            (((`Normal
                                                 (id, b, c, d, occur_loc_id))
                                              :: res), i) in
                                      let l =
                                        fst (List.fold_right fn l ([], 0)) in
                                      (_loc, (occur "_loc" action), def, l,
                                        cond, action)))))))
let _ =
  glr_at_rule__set__grammar
    (fun alm ->
       Earley_core.Earley.fsequence
         (Earley_core.Earley.option None
            (Earley_core.Earley.apply (fun x -> Some x)
               (Earley_core.Earley.alternatives
                  (List.cons
                     (Earley_core.Earley.fsequence_ignore
                        (Earley_core.Earley.char '[' '[')
                        (Earley_core.Earley.fsequence_ignore
                           (Earley_core.Earley.char '@' '@')
                           (Earley_core.Earley.fsequence_ignore
                              (Earley_core.Earley.string "unshared"
                                 "unshared")
                              (Earley_core.Earley.fsequence_ignore
                                 (Earley_core.Earley.char ']' ']')
                                 (Earley_core.Earley.empty ())))))
                     (List.cons
                        (Earley_core.Earley.fsequence_ignore
                           (Earley_core.Earley.char '@' '@')
                           (Earley_core.Earley.empty ())) [])))))
         (Earley_core.Earley.fsequence (glr_rule alm)
            (Earley_core.Earley.empty (fun r -> fun a -> ((a <> None), r)))))
let _ =
  Earley_core.Earley.set_grammar glr_rules
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.char '|' '|')))
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l)
                (Earley_core.Earley.fsequence (glr_at_rule false)
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '|' '|')
                      (Earley_core.Earley.empty (fun r -> r))))
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.fsequence (glr_at_rule true)
             (Earley_core.Earley.empty
                (fun r -> fun rs -> fun _default_0 -> r :: rs)))))
[@@@ocaml.text
  " Grammar for a single parser atom (including composite atoms such a a local\n    alternative given in braces). The semantic action is a pair [(boring, e)],\n    where [boring] is a boolean indicating whether the denoted parser produces\n    a boring value (i.e., an uninteresting result),  and [e] is the parser for\n    the atom (as an OCaml expression). "]
let glr_binding = Earley_core.Earley.declare_grammar "glr_binding"
let _ =
  Earley_core.Earley.set_grammar glr_binding
    (Earley_core.Earley.fsequence lident
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l) pattern
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.option None
                (Earley_core.Earley.apply (fun x -> Some x)
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '@' '@')
                      (Earley_core.Earley.fsequence pattern
                         (Earley_core.Earley.empty
                            (fun _default_0 -> _default_0))))))
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.option None
                   (Earley_core.Earley.apply (fun x -> Some x)
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char ':' ':')
                         (Earley_core.Earley.fsequence typexpr
                            (Earley_core.Earley.empty
                               (fun _default_0 -> _default_0))))))
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '=' '=')
                   (Earley_core.Earley.fsequence_position glr_rules
                      (Earley_core.Earley.empty
                         (fun str1 ->
                            fun pos1 ->
                              fun str2 ->
                                fun pos2 ->
                                  fun r ->
                                    let _loc_r = locate str1 pos1 str2 pos2 in
                                    fun ty ->
                                      fun prio ->
                                        fun args ->
                                          fun name ->
                                            `Parser
                                              (name, args, prio, ty, _loc_r,
                                                r)))))))))
let glr_bindings = Earley_core.Earley.declare_grammar "glr_bindings"
let _ =
  Earley_core.Earley.set_grammar glr_bindings
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence and_kw
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.option []
                   (Earley_core.Earley.fsequence let_binding
                      (Earley_core.Earley.fsequence_ignore and_kw
                         (Earley_core.Earley.empty
                            (fun _default_0 -> _default_0)))))
                (Earley_core.Earley.fsequence parser_kw
                   (Earley_core.Earley.fsequence glr_binding
                      (Earley_core.Earley.fsequence glr_bindings
                         (Earley_core.Earley.empty
                            (fun bs ->
                               fun b ->
                                 fun _default_0 ->
                                   fun cs ->
                                     fun _default_1 ->
                                       (List.map (fun b -> `Caml b) cs) @ (b
                                         :: bs))))))))
          (List.cons
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.option []
                   (Earley_core.Earley.fsequence_ignore and_kw
                      (Earley_core.Earley.fsequence let_binding
                         (Earley_core.Earley.empty
                            (fun _default_0 -> _default_0)))))
                (Earley_core.Earley.empty
                   (fun cs -> List.map (fun b -> `Caml b) cs))) [])))
let extra_structure = Earley_core.Earley.declare_grammar "extra_structure"
let _ =
  Earley_core.Earley.set_grammar extra_structure
    (Earley_core.Earley.fsequence_ignore let_kw
       (Earley_core.Earley.fsequence_ignore parser_kw
          (Earley_core.Earley.fsequence glr_binding
             (Earley_core.Earley.fsequence glr_bindings
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun bs -> fun b -> build_str_item _loc (b :: bs)))))))
let parser_args = Earley_core.Earley.declare_grammar "parser_args"
let _ =
  Earley_core.Earley.set_grammar parser_args
    (Earley_core.Earley.fsequence_ignore fun_kw
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l)
                (pattern_lvl (false, AtomPat))
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '@' '@')
             (Earley_core.Earley.fsequence pattern
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "->" "->")
                   (Earley_core.Earley.empty
                      (fun _default_0 ->
                         fun _default_1 -> (_default_1, _default_0))))))))
let extra_prefix_expressions =
  Earley_core.Earley.declare_grammar "extra_prefix_expressions"
let _ =
  Earley_core.Earley.set_grammar extra_prefix_expressions
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x) parser_args))
       (Earley_core.Earley.fsequence_ignore parser_kw
          (Earley_core.Earley.fsequence_position glr_rules
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun str1 ->
                           fun pos1 ->
                             fun str2 ->
                               fun pos2 ->
                                 fun r ->
                                   let _loc_r = locate str1 pos1 str2 pos2 in
                                   fun args ->
                                     let (args, e) =
                                       match args with
                                       | Some (args, prio) ->
                                           (args,
                                             (build_prio_alternatives _loc_r
                                                prio r))
                                       | None ->
                                           ([],
                                             (build_alternatives _loc_r r)) in
                                     List.fold_right
                                       (Exp.fun_ ~loc:_loc Nolabel None) args
                                       e)))))
let _ = add_reserved_id "parser"
