(*
  ======================================================================
  Copyright Christophe Raffalli & Rodolphe Lepigre
  LAMA, UMR 5127 - Université Savoie Mont Blanc

  christophe.raffalli@univ-savoie.fr
  rodolphe.lepigre@univ-savoie.fr

  This software contains implements a parser combinator library together
  with a syntax extension mechanism for the OCaml language.  It  can  be
  used to write parsers using a BNF-like format through a syntax extens-
  ion called pa_parser.

  This software is governed by the CeCILL-B license under French law and
  abiding by the rules of distribution of free software.  You  can  use,
  modify and/or redistribute it under the terms of the CeCILL-B  license
  as circulated by CEA, CNRS and INRIA at the following URL:

            http://www.cecill.info

  The exercising of this freedom is conditional upon a strong obligation
  of giving credits for everybody that distributes a software incorpora-
  ting a software ruled by the current license so as  all  contributions
  to be properly identified and acknowledged.

  As a counterpart to the access to the source code and rights to  copy,
  modify and redistribute granted by the  license,  users  are  provided
  only with a limited warranty and the software's author, the holder  of
  the economic rights, and the successive licensors  have  only  limited
  liability.

  In this respect, the user's attention is drawn to the risks associated
  with loading, using, modifying and/or developing  or  reproducing  the
  software by the user in light of its specific status of free software,
  that may mean that it is complicated  to  manipulate,  and  that  also
  therefore means that it is reserved  for  developers  and  experienced
  professionals having in-depth computer knowledge. Users are  therefore
  encouraged to load and test  the  software's  suitability  as  regards
  their requirements in conditions enabling the security of  their  sys-
  tems and/or data to be ensured and, more generally, to use and operate
  it in the same conditions as regards security.

  The fact that you are presently reading this means that you  have  had
  knowledge of the CeCILL-B license and that you accept its terms.
  ======================================================================
*)

open Asttypes
open Parsetree
open Longident
open Pa_ocaml_prelude
open Pa_lexing
open Helper

#define LOCATE locate

type action =
  | Default
  | Normal  of expression
  | DepSeq  of ((expression -> expression) * expression option * expression)

let occur id e =
  Iter.do_local_ident := (fun s -> if s = id then raise Exit);
  try
    (match e with
    | Default -> ()
    | Normal e -> Iter.iter_expression e;
    | DepSeq (_,e1,e2) -> Iter.iter_option Iter.iter_expression e1; Iter.iter_expression e2);
    false
  with
    Exit -> true

let find_locate () =
  try Some(Exp.ident {txt = Lident(Sys.getenv "LOCATE"); loc = Location.none})
  with Not_found -> None

let mkpatt _loc (id, p) =
  match p, find_locate () with
  | (None  , _     ) -> Pat.var ~loc:_loc {txt = id; loc = _loc}
  | (Some p, None  ) -> <:pat<$p$ as $lid:id$>>
  | (Some p, Some _) -> <:pat<(_,$p$) as $lid:id$>>

let mkpatt' _loc (id,p) =  match p with
    None -> <:pat<$lid:id$>>
  | Some p -> <:pat<$p$ as $lid:id$>>

let cache_filter = Hashtbl.create 101

let filter _loc visible r =
  match find_locate (), visible with
  | Some(f2), true ->
     let f = <:expr<fun str pos str' pos' x -> ($f2$ str pos str' pos', x)>> in
     (try
       Hashtbl.find cache_filter (f,r)
     with Not_found ->
       let res = <:expr<Earley.apply_position $f$ $r$>> in
       Hashtbl.add cache_filter (f,r) res;
       res)
  | _ -> r


let rec build_action _loc occur_loc ids e =
  let e1 =
    List.fold_left (fun e ((id,x),visible) ->
        match find_locate (), visible with
        | Some(_), true ->
           <:expr<fun $pat:mkpatt _loc (id,x)$ ->
            let ($lid:"_loc_"^id$, $lid:id$) = $lid:id$ in $e$>>
        | _ ->
           <:expr<fun $pat:mkpatt' _loc (id,x)$ -> $e$>>
      ) e (List.rev ids)
  in
  match find_locate (), occur_loc with
    | Some(locate2), true ->
       <:expr<fun __loc__start__buf __loc__start__pos
                  __loc__end__buf __loc__end__pos ->
                  let _loc = $locate2$ __loc__start__buf __loc__start__pos
                                        __loc__end__buf __loc__end__pos in $e1$>>
    | _ -> e1

let apply_option _loc opt visible e =
  let fn e f d =
    match d with
       None   -> <:expr< Earley.$lid:f$ None (Earley.apply (fun x -> Some x) $e$) >>
    | Some d -> <:expr< Earley.$lid:f$ $d$ $e$ >>
  in
  let gn e f d =
    match d with
      None   -> <:expr< Earley.apply List.rev (Earley.$lid:f$ [] (Earley.apply (fun x y -> x::y) $e$)) >>
    | Some d -> <:expr< Earley.$lid:f$ $d$ $e$ >>
  in
  let kn e = function
    | None   -> e
    | Some _ -> <:expr< Earley.greedy $e$ >>
  in
  filter _loc visible (match opt with
    `Once -> e
  | `Option(d,g)    -> kn (fn e "option" d) g
  | `Greedy       -> <:expr< Earley.greedy $e$ >>
  | `Fixpoint(d,g)  -> kn (gn e "fixpoint" d) g
  | `Fixpoint1(d,g) -> kn (gn e "fixpoint1" d) g
  )

let default_action _loc l =
  let l = List.filter (function `Normal((("_",_),false,_,_,_)) -> false
                              | _ -> true) l
  in
  let l = List.map (function `Normal((id,_),_,_,_,_) -> <:expr<$lid:id$>>
                           | _ -> assert false) l
  in
  <:expr<$tuple:l$>>

let from_opt ov d = match ov with None -> d | Some v -> v

let dash =
  let fn str pos =
    let (c,str',pos') = Input.read str pos in
    if c = '-' then
      let (c',_,_) = Input.read str' pos' in
      if c' = '>' then Earley.give_up ()
      else ((), str', pos')
    else Earley.give_up ()
  in
  Earley.black_box fn (Charset.singleton '-') false "-"

module Ext(In:Extension) = struct
  include In

  let expr_arg = expression_lvl (NoMatch, next_exp App)

  let build_rule (_loc,occur_loc,def, l, condition, action) =
      let iter, action = match action with
	| Normal a -> false, a
	| Default -> false, default_action _loc l
	| DepSeq(def, cond, a) ->
           true, (match cond with
		 | None -> def a
		 | Some cond ->
		    def (<:expr<if $cond$ then $a$ else Earley.fail ()>>))
      in

      let rec fn ids l = match l with
	  [] -> assert false
	| [`Normal(id,_,e,opt,occur_loc_id)] ->
	   let e = apply_option _loc opt occur_loc_id e in
	   let f = match find_locate (), occur_loc with
	     | Some _, true -> "apply_position"
	     | _ -> "apply"
	   in
	   (match action.pexp_desc with
		Pexp_ident({ txt = Lident id'}) when ids = [] && fst id = id' && f = "apply" -> e
	      | _ ->
                 let a = build_action _loc occur_loc ((id,occur_loc_id)::ids) action in
                 <:expr<Earley.$lid:f$ $a$ $e$>>)

	| `Normal(id,_,e,opt,occur_loc_id) :: ls ->
	   let e = apply_option _loc opt occur_loc_id e in
           let a = fn ((id,occur_loc_id)::ids) ls in
           <:expr<Earley.$lid:"fsequence"$ $e$ $a$>>
      in
      let res = fn [] l in
      let res = if iter then <:expr<Earley.iter $res$>> else res in
      def, condition, res

  let apply_def_cond _loc r =
    let (def,cond,e) = build_rule r in
    match cond with
      None -> def e
    | Some c ->
      def <:expr<if $c$ then $e$ else Earley.fail ()>>

  let apply_def_cond_list _loc r acc =
    let (def,cond,e) = build_rule r in
    match cond with
    | None -> def (<:expr<$e$ :: $acc$>>)
    | Some c -> def (<:expr<(if $c$ then [$e$] else []) @ $acc$>>)

  let apply_def_cond_prio _loc arg r acc =
    let (def,cond,e) = build_rule r in
    match cond with
    | None -> def (<:expr<((fun _ -> true), $e$) :: $acc$>>)
    | Some c -> def (<:expr<((fun $pat:arg$ -> $c$), $e$) :: $acc$>>)

  let build_alternatives _loc ls =
    (* FIXME: warning if useless @| ? *)
    let ls = List.map snd ls in
    match ls with
    | [] -> <:expr<Earley.fail ()>>
    | [r] -> apply_def_cond _loc r
    | _::_::_ ->
        let l = List.fold_right (apply_def_cond_list _loc) ls (<:expr<[]>>) in
        <:expr<Earley.alternatives $l$>>

  let build_prio_alternatives _loc arg ls =
    let l0, l1 = List.partition fst ls in
    let l0 = List.map snd l0 and l1 = List.map snd l1 in
    let l1 = List.fold_right (apply_def_cond_prio _loc arg) l1 (<:expr<[]>>) in
    let l0 = List.fold_right (apply_def_cond_list _loc) l0 (<:expr<[]>>) in
    <:expr<($l1$, (fun $pat:arg$ -> $l0$))>>

  let build_str_item _loc l =
    let rec fn = function
      | []                 -> ([], [], [])
      | `Caml b::l ->
         let (str1, str2, str3) = fn l in
         (str1, str2, b :: str3)
      | `Parser(name,args,prio,ty,_loc_r,r)::l ->
          let (str1, str2, str3) = fn l in
          let pname = <:pat<$lid:name$>> in
          let coer f =
            match ty with
            | None -> f
            | Some ty -> <:expr<($f$ : $ty$)>>
          in
          let args_pat =<:pat< $tuple:args$ >> in
          let (str1,str2) =
            match args,prio with
            | [], None ->
               let r = coer (build_alternatives _loc_r r) in
               (<:struct<let $pat:pname$ = Earley.declare_grammar $string:name$>>
                 @ str1,
                <:struct<let _ = Earley.set_grammar $lid:name$ $r$>> @ str2)
            | _, None ->
               let r = coer (build_alternatives _loc_r r) in
               let set_name = name ^ "__set__grammar" in
               (<:struct<let ($pat:pname$,$lid:set_name$) =
                 Earley.grammar_family $string:name$>> @str1,
                <:struct<let _ = $lid:set_name$ (fun $pat:args_pat$ -> $r$)>>
                @ str2)

            | [], Some prio ->
               let r = coer (build_prio_alternatives _loc_r prio r) in
               let set_name = name ^ "__set__grammar" in
               (<:struct<let ($pat:pname$,$lid:set_name$) =
                 Earley.grammar_prio $string:name$>> @ str1,
                <:struct<let _ = $lid:set_name$ $r$>> @ str2)
            | args, Some prio ->
               let r = coer (build_prio_alternatives _loc_r prio r) in
               let set_name = name ^ "__set__grammar" in
               (<:struct<let ($pat:pname$,$lid:set_name$) =
                 Earley.grammar_prio_family $string:name$>> @ str1,
                <:struct<let _ = $lid:set_name$ (fun $pat:args_pat$ -> $r$)>>
                 @ str2)
          in
          let str2 =
            match args, prio with
            | ([], _) | ([_], None) -> str2
            | _ ->
              let rec currify acc n = function
                  [] ->
                  begin
                    match prio with
                    | None -> <:expr<$lid:name$ $tuple:List.rev acc$ >>
                    | Some _ -> <:expr<fun __curry__prio -> $lid:name$ $tuple:List.rev acc$ __curry__prio >>
                  end
                | a::l ->
                   let v = "__curry__varx"^string_of_int n in
                   let acc = <:expr< $lid:v$ >> :: acc in
                   <:expr<fun $lid:v$ -> $currify acc (n+1) l$>>
              in
              let f = currify [] 0 args in
              <:struct<let $pat:pname$ = $f$>> @ str2
          in
          (str1,str2,str3)

    in
    let (str1, str2, str3) = fn l in
    if str3 = [] then
      str1 @ str2
    else
      str1 @ <:struct<let rec $bindings:str3$>> @ str2


  let parser glr_sequence =
    | '{' r:glr_rules '}'
     -> (true, build_alternatives _loc_r r)
    | "EOF" oe:glr_opt_expr
     -> (oe <> None, <:expr<Earley.eof $from_opt oe <:expr<()>>$ >>)
    | "EMPTY" oe:glr_opt_expr
     -> (oe <> None, <:expr<Earley.empty $from_opt oe <:expr<()>>$ >>)
    | "FAIL" e:expr_arg
     -> (false, <:expr<Earley.fail $e$>>)
    | "DEBUG" e:expr_arg
     -> (false, <:expr<Earley.debug $e$>>)
    | "ANY"
     -> (true, <:expr<Earley.any>>)
    | "CHR" e:expr_arg oe:glr_opt_expr
     -> (oe <> None, <:expr<Earley.char $e$ $from_opt oe e$>>)
    | c:char_litteral oe:glr_opt_expr
     -> let e = <:expr<$char:c$>> in
        (oe <> None, <:expr<Earley.char $e$ $from_opt oe e$>>)
    | "STR" e:expr_arg oe:glr_opt_expr
     -> (oe <> None, <:expr<Earley.string $e$ $from_opt oe e$>>)
    | "ERROR" e:expr_arg
     -> (true, <:expr<Earley.error_message (fun () -> $e$)>>)
    | (s,_):string_litteral oe:glr_opt_expr
     -> if String.length s = 0 then Earley.give_up ();
        let s = <:expr<$string:s$>> in
        let e = from_opt oe s in
        (oe <> None, <:expr<Earley.string $s$ $e$>>)
    | "RE" e:expr_arg opt:glr_opt_expr
     -> begin
          let act = <:expr<fun groupe -> $from_opt opt <:expr<groupe 0>>$ >> in
          match e.pexp_desc with
          | Pexp_ident { txt = Lident id } ->
              let id =
                let l = String.length id in
                if l > 3 && String.sub id (l - 3) 3 = "_re" then
                  String.sub id 0 (l - 3)
                else id
              in
              (true, <:expr<EarleyStr.regexp ~name:$string:id$ $e$ $act$>>)
          | _ -> (true, <:expr<EarleyStr.regexp $e$ $act$>>)
        end
    | "BLANK" oe:glr_opt_expr
     -> let e = from_opt oe <:expr<()>> in
        (oe <> None, <:expr<Earley.with_blank_test $e$>>)
    | dash oe:glr_opt_expr
     -> let e = from_opt oe <:expr<()>> in
        (oe <> None, <:expr<Earley.no_blank_test $e$>>)
    | s:regexp_litteral oe:glr_opt_expr
     -> let opt = from_opt oe <:expr<groupe 0>> in
        let es = String.escaped s in
        let act = <:expr<fun groupe -> $opt$>> in
        (true, <:expr<EarleyStr.regexp ~name:$string:es$ $string:s$ $act$>>)
    | s:new_regexp_litteral opt:glr_opt_expr
     -> begin
          let es = String.escaped s in
          let s = "\\(" ^ s ^ "\\)" in
          let re = <:expr<Earley.regexp ~name:$string:es$ $string:s$>> in
          match opt with
          | None   -> (true, re)
          | Some e -> (true, <:expr<Earley.apply (fun group -> $e$) $re$>>)
        end
    | id:value_path
     -> (true, <:expr<$longident:id$>>)
    | "(" e:expression ")"
     -> (true, e)


  and parser glr_opt_expr = {'[' expression ']'}?

  and parser glr_option =
    | '*' e:glr_opt_expr g:'$'? -> `Fixpoint(e,g)
    | '+' e:glr_opt_expr g:'$'? -> `Fixpoint1(e,g)
    | '?' e:glr_opt_expr g:'$'? -> `Option(e,g)
    | '$'                       -> `Greedy
    | EMPTY                     -> `Once


  and parser glr_ident =
    | p:(pattern_lvl (true, ConstrPat)) ':' ->
        begin
          match p.ppat_desc with
          | Ppat_alias(p, { txt = id }) -> (Some true, (id, Some p))
          | Ppat_var { txt = id } -> (Some (id <> "_"), (id, None))
          | Ppat_any -> (Some false, ("_", None))
          | _ -> (Some true, ("_", Some p))
        end
    | EMPTY -> (None, ("_", None))

  and parser glr_left_member =
     {(cst',id):glr_ident (cst,s):glr_sequence opt:glr_option ->
       `Normal(id, (from_opt cst' (opt <> `Once || cst)),s,opt) }+

  and parser glr_let =
    | let_kw r:rec_flag lbs:let_binding in_kw l:glr_let ->
        (fun x -> Exp.let_ ~loc:_loc r lbs (l x))
    | EMPTY ->
        (fun x -> x)

  and parser glr_cond = {_:when_kw e:expression}?

  and parser glr_action alm =
    | "->>" r:(glr_rule alm) -> let (a,b,c) = build_rule r in DepSeq (a,b,c)
    | arrow_re action:(if alm then expression else expression_lvl (Let, Seq)) no_semi -> Normal action
    | EMPTY -> Default

  and parser glr_rule alm =
    | def:glr_let l:glr_left_member condition:glr_cond action:(glr_action alm) ->
        let l = fst (List.fold_right (fun x (res,i) ->
          match x with
          | `Normal(("_",a),true,c,d) ->
              (`Normal(("_default_"^string_of_int i,a),true,c,d,false)::res, i+1)
          | `Normal(id, b,c,d) ->
              let occur_loc_id = fst id <> "_" && occur ("_loc_"^fst id) action in
              (`Normal(id, b,c,d,occur_loc_id)::res, i)) l ([], 0))
        in
        let occur_loc = occur ("_loc") action in
        (_loc, occur_loc, def, l, condition, action)

  and parser glr_at_rule alm = a:{'@' | '[' '@' "unshared" ']' }? r:(glr_rule alm) -> ((a <> None), r)

  and parser glr_rules = '|'? rs:{ r:(glr_at_rule false) _:'|'}* r:(glr_at_rule true)
      -> r::rs

  let parser glr_binding =
    name:lident args:pattern* prio:{_:'@' pattern}? ty:{':' typexpr}? '=' r:glr_rules
      -> `Parser(name,args,prio,ty,_loc_r,r)

  let parser glr_bindings =
    | cs:{_:and_kw let_binding}?[[]] -> List.map (fun b -> `Caml b) cs
    | and_kw cs:{let_binding _:and_kw}?[[]] parser_kw b:glr_binding l:glr_bindings
          -> (List.map (fun b -> `Caml b) cs) @ b::l

  let extra_structure =
    let p = parser let_kw parser_kw b:glr_binding l:glr_bindings -> build_str_item _loc (b::l) in
    p :: extra_structure

  let extra_prefix_expressions =
    let p = parser (args,prio):{_:parser_kw -> ([], None)
                               | _:fun_kw args:(pattern_lvl(false,AtomPat))* '@'
                                          prio:pattern _:arrow_re _:parser_kw
                                             -> (args,Some prio)
                               | _:function_kw arg:pattern '@'
                                       prio:pattern _:arrow_re _:parser_kw
                                             -> ([arg],Some prio)
                               }   r:glr_rules
      ->
      let r = match prio with
        | None -> build_alternatives _loc_r r
        | Some prio -> build_prio_alternatives _loc_r prio r
      in
      List.fold_right (fun arg r ->
          <:expr< fun $arg$ -> $r$>>) args r
    in
    p :: extra_prefix_expressions

  let _ = add_reserved_id "parser"
end
