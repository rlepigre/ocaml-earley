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
open Pa_ast
open Pa_lexing

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
  try
    let l = Sys.getenv "LOCATE" in
    Some(exp_ident Location.none l)
  with Not_found -> None

let mkpatt _loc (id, p) = match p, find_locate () with
    None, _ -> pat_ident _loc id
  | Some p, None -> ppat_alias _loc p id
  | Some p, Some _ ->
     ppat_alias _loc (loc_pat _loc (Ppat_tuple[loc_pat _loc Ppat_any; p])) id

let mkpatt' _loc (id,p) =  match p with
    None -> pat_ident _loc id
  | Some p -> ppat_alias _loc p id

let cache_filter = Hashtbl.create 101

let filter _loc visible r =
  match find_locate (), visible with
  | Some(f2), true ->
     let f =
       exp_fun _loc "x" (
	 exp_fun _loc "str" (
	   exp_fun _loc "pos" (
	     exp_fun _loc "str'" (
	       exp_fun _loc "pos'" (
		 exp_tuple _loc [
  		   exp_apply _loc f2
		     [exp_ident _loc "str";
		      exp_ident _loc "pos";
		      exp_ident _loc "str'";
		      exp_ident _loc "pos'"];
		   exp_ident _loc "x"])))))
     in
     (try
       let res = Hashtbl.find cache_filter (f,r) in
       res
     with Not_found ->
       let res = exp_apply _loc (exp_glr_fun _loc "apply_position") [f; r] in
       Hashtbl.add cache_filter (f,r) res;
       res)
  | _ -> r


let rec build_action _loc occur_loc ids e =
  let e = match find_locate (), occur_loc with
    | Some(locate2), true ->
       exp_fun _loc "__loc__start__buf" (
	 exp_fun _loc "__loc__start__pos" (
	   exp_fun _loc "__loc__end__buf" (
	     exp_fun _loc "__loc__end__pos" (
	       loc_expr _loc (Pexp_let(Nonrecursive, [
	         value_binding _loc (pat_ident _loc "_loc")
			       (exp_apply _loc locate2 [exp_ident _loc "__loc__start__buf";
							exp_ident _loc "__loc__start__pos";
							exp_ident _loc "__loc__end__buf";
							exp_ident _loc "__loc__end__pos"])], e))))))
    | _ -> e
  in
  List.fold_left (fun e ((id,x),visible) ->
    match find_locate (), visible with
    | Some(_), true ->
      loc_expr _loc (
	pexp_fun(nolabel, None,
	  mkpatt _loc (id,x),
	  loc_expr _loc (Pexp_let(Nonrecursive,
	    [value_binding _loc (loc_pat _loc (Ppat_tuple([
		loc_pat _loc (Ppat_var (id_loc ("_loc_"^id) _loc));
		loc_pat _loc (Ppat_var (id_loc id _loc))])))
	     (loc_expr _loc (Pexp_ident((id_loc (Lident id) _loc))))],
	    e))))
    | _ ->
      loc_expr _loc (pexp_fun(nolabel, None, mkpatt' _loc (id,x), e))
  ) e (List.rev ids)

let apply_option _loc opt visible e =
  let fn e f d =
    match d with
       None   -> <:expr< Decap.$lid:f$ None (Decap.apply (fun x -> Some x) $e$) >>
    | Some d -> <:expr< Decap.$lid:f$ $d$ $e$ >>
  in
  let gn e f d =
    match d with
      None   -> <:expr< Decap.apply List.rev (Decap.$lid:f$ [] (Decap.apply (fun x y -> x::y) $e$)) >>
    | Some d -> <:expr< Decap.$lid:f$ $d$ $e$ >>
  in
  let kn e = function
    | None   -> e
    | Some _ -> <:expr< Decap.greedy $e$ >>
  in
  filter _loc visible (match opt with
    `Once -> e
  | `Option(d,g)    -> kn (fn e "option" d) g
  | `Greedy       -> <:expr< Decap.greedy $e$ >>
  | `Fixpoint(d,g)  -> kn (gn e "fixpoint" d) g
  | `Fixpoint1(d,g) -> kn (gn e "fixpoint1" d) g
  )

let default_action _loc l =
  let l = List.filter (function `Normal((("_",_),false,_,_,_)) -> false | `Ignore -> false | _ -> true) l in
  let l = List.map (function `Normal((id,_),_,_,_,_) -> exp_ident _loc id | _ -> assert false) l in
  let rec fn = function
    | [] -> exp_unit _loc
    | [x] -> x
    | _::_ as l ->
       exp_tuple _loc l
  in
  fn l

module Ext = functor(In:Extension) ->
struct
  include In

  let glr_rules = Decap.declare_grammar "glr_rules"
  let glr_rule, set_glr_rule = Decap.grammar_family "glr_rule"

  let location_name_re = "_loc\\([a-zA-Z0-9_']*\\)"

  let parser glr_parser =
    | parser_kw p:glr_rules -> p

  let glr_binding = Decap.declare_grammar "glr_binding"
  let _ = Decap.set_grammar glr_binding (
    parser
      name:lident arg:(pattern_lvl AsPat)? ty:{':' typexpr}? '=' r:glr_rules l:{_:and_kw glr_binding}?[[]] ->
    (name,arg,ty,r)::l)

  let parser glr_struct_item =
    | let_kw parser_kw l:glr_binding ->
		  let rec fn = function
		    | [] -> [], []
		    | (name,arg,ty,r)::l ->
		       let str1, str2 = fn l in
		       let pat_name = loc_pat _loc (Ppat_var (id_loc name _loc)) in
		       let pname = match ty, arg with
			   None, _-> pat_name
			 | Some ty, None ->
			    let ptyp_ty = loc_typ _loc (Ptyp_poly ([], ty)) in
			    loc_pat _loc (Ppat_constraint(pat_name, ptyp_ty))
			 | Some ty, Some _ ->
			    let ptyp_ty = loc_typ _loc (Ptyp_poly ([], ty)) in
			    loc_pat _loc (Ppat_constraint(pat_name,
				  loc_typ _loc (Ptyp_arrow(nolabel,
							   loc_typ _loc (Ptyp_var "'type_of_arg"),
							   ptyp_ty))))
		       in
		       (match arg with
		       | None ->
			  let ddg = exp_glr_fun _loc "declare_grammar" in
			  let strname = loc_expr _loc (Pexp_constant (const_string name)) in
			  let name = loc_expr _loc (Pexp_ident(id_loc (Lident name) _loc)) in
			  let e = loc_expr _loc (Pexp_apply(ddg, [nolabel, strname])) in
			  let l = value_binding ~attributes:[] _loc pname e in
			  let dsg = exp_glr_fun _loc "set_grammar" in
			  let ev = loc_expr _loc (Pexp_apply(dsg, [(nolabel,name);(nolabel,r)])) in
			  (loc_str _loc (Pstr_value (Nonrecursive, [l])) :: str1),
			  (loc_str _loc (pstr_eval ev) :: str2)
			| Some arg ->
			  let dgf = exp_glr_fun _loc "grammar_family" in
			  let set_name = name ^ "__set__grammar" in
			  let strname = loc_expr _loc (Pexp_constant (const_string name)) in
			  let sname = loc_expr _loc (Pexp_ident(id_loc (Lident set_name) _loc)) in
			  let psname = loc_pat _loc (Ppat_var (id_loc set_name _loc)) in
			  let ptuple = loc_pat _loc (Ppat_tuple [pname;psname]) in
			  let e = loc_expr _loc (Pexp_apply(dgf, [nolabel, strname])) in
			  let l = value_binding ~attributes:[] _loc ptuple e in
			  let fam = loc_expr _loc (pexp_fun(nolabel,None,arg,r)) in
			  let ev = loc_expr _loc (Pexp_apply(sname, [(nolabel,fam)])) in
			  (loc_str _loc (Pstr_value (Nonrecursive, [l])) :: str1),
			  (loc_str _loc (pstr_eval ev) :: str2)
(*			   <:structure< let $pname$, $lid:set_name$ = Decap.grammar_family $string:name$>> @ str1,
			   <:structure< let _ = $lid:set_name$ (fun $arg$ -> $r$) >> @ str2*) )
		  in
		  let str1, str2 = fn l in
		  str1 @ str2

  let extra_prefix_expressions = glr_parser::extra_prefix_expressions
  let extra_structure = glr_struct_item::extra_structure

  let _ = add_reserved_id "parser"

  let parser glr_opt_expr =
      e:{ CHR('[') e:expression CHR(']') }? -> e

  let parser glr_option =
    | '*' e:glr_opt_expr g:'#'? -> `Fixpoint(e,g)
    | '+' e:glr_opt_expr g:'#'? -> `Fixpoint1(e,g)
    | '?' e:glr_opt_expr g:'#'? -> `Option(e,g)
    | '#'                -> `Greedy
    | EMPTY -> `Once

  let parser glr_sequence =
    | CHR('{') r:glr_rules CHR('}') -> true, r
    | STR("EOF") opt:glr_opt_expr ->
       let e = match opt with None -> exp_unit _loc | Some e -> e in
       (opt <> None, exp_apply _loc (exp_glr_fun _loc "eof") [e])
    | STR("EMPTY") opt:glr_opt_expr ->
       let e = match opt with None -> exp_unit _loc | Some e -> e in
       (opt <> None, exp_apply _loc (exp_glr_fun _loc "empty") [e])
    | STR("FAIL") e:(expression_lvl (NoMatch, next_exp App)) ->
       (false, exp_apply _loc (exp_glr_fun _loc "fail") [e])
    | STR("DEBUG") e:(expression_lvl (NoMatch, next_exp App)) ->
       (false, exp_apply _loc (exp_glr_fun _loc "debug") [e])
    | STR("ANY") ->
       (true, exp_glr_fun _loc "any")
    | STR("CHR") e:(expression_lvl (NoMatch, next_exp App)) opt:glr_opt_expr ->
       let o = match opt with None -> e | Some e -> e in
       (opt <> None, exp_apply _loc (exp_glr_fun _loc "char") [e; o])
    | c:char_litteral opt:glr_opt_expr ->
       let e = exp_char _loc_c c in
       let o = match opt with None -> e | Some e -> e in
       (opt <> None, exp_apply _loc (exp_glr_fun _loc "char") [e; o])
    | STR("STR") e:(expression_lvl (NoMatch, next_exp App)) opt:glr_opt_expr ->
       let o = match opt with None -> e | Some e -> e in
       (opt <> None, exp_apply _loc (exp_glr_fun _loc "string") [e; o])
    | s:string_litteral opt:glr_opt_expr ->
       (opt <> None,
        (if String.length s = 0 then
	  Decap.give_up "Empty string litteral in rule.";
	let e = exp_string _loc_s s in
	let opt = match opt with None -> e | Some e -> e in
	exp_apply _loc (exp_glr_fun _loc "string") [e; opt]))
    | STR("RE") e:(expression_lvl (NoMatch, next_exp App))  opt:glr_opt_expr ->
       let opt = match opt with
	 | None -> exp_apply _loc (exp_ident _loc "groupe") [exp_int _loc 0]
	 | Some e -> e
       in
       (match e.pexp_desc with
	  Pexp_ident { txt = Lident id } ->
	  let id =
	    let l = String.length id in
	    if l > 3 && String.sub id (l - 3) 3 = "_re" then String.sub id 0 (l - 3) else id
	  in
	  (true, exp_lab_apply _loc (exp_glr_fun _loc "regexp") [labelled "name", exp_string _loc id; nolabel, e; nolabel, exp_fun _loc "groupe" opt])
	| _ ->
	  (true, exp_apply _loc (exp_glr_fun _loc "regexp") [e; exp_fun _loc "groupe" opt]))

    | s:regexp_litteral opt:glr_opt_expr ->
       let opt = match opt with
	 | None -> exp_apply _loc (exp_ident _loc "groupe") [exp_int _loc 0]
	 | Some e -> e
       in
       (true, exp_lab_apply _loc (exp_glr_fun _loc "regexp") [labelled "name", exp_string _loc_s (String.escaped s);
							  nolabel, exp_string _loc_s s;
							  nolabel, exp_fun _loc_opt "groupe" opt])

    | id:value_path -> (true, loc_expr _loc (Pexp_ident(id_loc id _loc_id)))

    | "(" e:expression ")" -> (true, e)

  let parser glr_ident =
    | p:(pattern_lvl ConstrPat) ':' ->
	(match p.ppat_desc with
	 | Ppat_alias(p, { txt = id }) -> (Some true, (id, Some p))
	 | Ppat_var { txt = id } -> (Some (id <> "_"), (id, None))
         | Ppat_any -> (Some false, ("_", None))
	 | _ -> (Some true, ("_", Some p)))
    | EMPTY -> (None, ("_", None))

  let dash = Decap.black_box
    (fun str pos ->
       let c,str',pos' = Input.read str pos in
       if c = '-' then
         let c',_,_ = Input.read str' pos' in
         if c' = '>' then Decap.give_up "\'-\' expected"
         else (), str', pos'
      else
        Decap.give_up "\'-\' expexted"
    ) (Charset.singleton '-') false ("-")


  let fopt x y = match x with Some x -> x | None -> y
  let parser glr_left_member =
    | i:{(cst',id):glr_ident (cst,s):glr_sequence opt:glr_option -> `Normal(id, (fopt cst' (opt <> `Once || cst)),s,opt)}
      l:{(cst',id):glr_ident (cst,s):glr_sequence opt:glr_option -> `Normal(id, (fopt cst' (opt <> `Once || cst)),s,opt) | dash -> `Ignore }* -> i::l

  let glr_let = Decap.declare_grammar "glr_let"
  let _ = Decap.set_grammar glr_let (
    parser
    | let_kw r:rec_flag lbs:let_binding in_kw l:glr_let -> (fun x -> loc_expr _loc (Pexp_let(r,lbs,l x)))
    | EMPTY -> (fun x -> x)
  )

  let parser glr_cond =
    | when_kw e:expression -> Some e
    | EMPTY -> None

  let build_rule (_loc,occur_loc,def, l, condition, action) =
      let iter, action = match action with
	| Normal a -> false, a
	| Default -> false, default_action _loc l
	| DepSeq(def, cond, a) ->
           true, (match cond with
		 | None -> def a
		 | Some cond ->
		    def (loc_expr _loc (Pexp_ifthenelse(cond,a,Some (exp_apply _loc (exp_glr_fun _loc "fail") [exp_string _loc ""])))))
      in

      let rec fn first ids l = match l with
	  [] -> assert false
	| `Ignore::ls -> assert false
	| `Normal(id,cst,e,opt,oc)::`Ignore::ls ->
	   let e =  exp_apply _loc (exp_glr_fun _loc "ignore_next_blank") [e] in
	   fn first ids (`Normal(id,cst,e,opt,oc)::ls)
	| [`Normal(id,_,e,opt,occur_loc_id)] ->
	   let e = apply_option _loc opt occur_loc_id e in
	   let f = match find_locate (), first && occur_loc with
	     | Some _, true -> "apply_position"
	     | _ -> "apply"
	   in
	   (match action.pexp_desc with
		Pexp_ident({ txt = Lident id'}) when fst id = id' && f = "apply" -> e
	   | _ ->
	      exp_apply _loc (exp_glr_fun _loc f) [build_action _loc occur_loc ((id,occur_loc_id)::ids) action; e])

	| [`Normal(id,_,e,opt,occur_loc_id); `Normal(id',_,e',opt',occur_loc_id') ] ->
	   let e = apply_option _loc opt occur_loc_id e in
	   let e' = apply_option _loc opt' occur_loc_id' e' in
	   let f = match find_locate (), first && occur_loc with
	     | Some _, true -> "sequence_position"
	     | _ -> "sequence"
	   in
	   exp_apply _loc (exp_glr_fun _loc f) [e; e'; build_action _loc occur_loc
	((id,occur_loc_id)::(id',occur_loc_id')::ids) action]

	| `Normal(id,_,e,opt,occur_loc_id) :: ls ->
	   let e = apply_option _loc opt occur_loc_id e in
	   let f = match find_locate (), first && occur_loc with
	     | Some _, true -> "fsequence_position"
	     | _ -> "fsequence"
	   in
	   exp_apply _loc (exp_glr_fun _loc f) [e; fn false ((id,occur_loc_id)::ids) ls]
      in
      let res = fn true [] l in
      let res = if iter then exp_apply _loc (exp_glr_fun _loc "iter") [res] else res in
      def, condition, res

  let parser glr_action alm =
    | "->>" r:(glr_rule alm) -> let (a,b,c) = build_rule r in DepSeq (a,b,c)
    | arrow_re action:(if alm then expression else expression_lvl(Let,Seq)) no_semi -> Normal action
    | EMPTY -> Default

  let _ = set_glr_rule (fun alm ->
    parser
      | def:glr_let l:glr_left_member condition:glr_cond action:(glr_action alm) ->
      let l = fst (List.fold_right (fun x (res,i) ->
	match x with
	  `Normal(("_",a),true,c,d) ->
	  (`Normal(("_default_"^string_of_int i,a),true,c,d,false)::res, i+1)
	| `Normal(id, b,c,d) ->
	   let occur_loc_id = fst id <> "_" && occur ("_loc_"^fst id) action in
	   (`Normal(id, b,c,d,occur_loc_id)::res, i)
	| `Ignore -> (`Ignore::res,i)) l ([], 0))
      in
      let occur_loc = occur ("_loc") action in
      (_loc, occur_loc, def, l, condition, action))

  let apply_def_cond _loc arg =
    let (def,cond,e) = build_rule arg in
    match cond with
      None -> def e
    | Some c ->
      def (loc_expr _loc (Pexp_ifthenelse(c,e,Some (exp_apply _loc (exp_glr_fun _loc "fail") [exp_string _loc ""]))))

  let build_alternatives _loc ls =
    match ls with
    | [] -> exp_apply _loc (exp_glr_fun _loc "fail") [exp_string _loc ""]
    | [r] -> apply_def_cond _loc r
    | elt1::elt2::_ ->
        let l = List.fold_right (fun r y ->
          let (def,cond,e) = build_rule r in
          match cond with
          | None -> def (exp_Cons _loc e y)
          | Some c -> def (loc_expr _loc (Pexp_let(Nonrecursive,[value_binding _loc (pat_ident _loc "y") y],
                                loc_expr _loc (Pexp_ifthenelse(c,exp_Cons _loc
                                 e (exp_ident _loc "y"), Some (exp_ident _loc "y"))))))
          ) ls (exp_Nil _loc)
        in
        exp_apply _loc (exp_glr_fun _loc "alternatives") [l]

  let _ = Decap.set_grammar glr_rules (
    parser
    | '|'? rs:{ r:(glr_rule false) '|' -> r}* r:(glr_rule true) ->
      build_alternatives _loc (rs@[r]))

end
