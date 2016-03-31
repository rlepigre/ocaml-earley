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

open Input
open Decap
open Asttypes
open Parsetree
open Pa_ast
open Pa_lexing

(* Some references for the handling of command-line arguments. *)
type entry = FromExt | Impl | Intf

let entry : entry ref         = ref FromExt
let fast  : bool ref          = ref false
let file  : string option ref = ref None
let ascii : bool ref          = ref false

(* Location function. *)
let locate str pos str' pos' =
  Lexing.(
    let s = Input.lexing_position str pos in
    let e = Input.lexing_position str' pos' in
    Location.({loc_start = s; loc_end = e; loc_ghost = false}))

#define LOCATE locate

(* OCaml grammar entry points. *)
type entry_point =
  | Implementation of Parsetree.structure_item list grammar * blank
  | Interface      of Parsetree.signature_item list grammar * blank

(* Initial parser module, starting point of the functorial interface. *)
module Initial =
  struct

    (* Default command line arguments. *)
    let spec : (Arg.key * Arg.spec * Arg.doc) list =
      [ ("--ascii", Arg.Set ascii,
          "Output ASCII text instead of serialized AST.")
      ; ("--impl", Arg.Unit (fun () -> entry := Impl),
          "Treat file as an implementation.")
      ; ("--intf", Arg.Unit (fun () -> entry := Intf),
          "Treat file as an interface.")
      ; ("--unsafe", Arg.Set fast,
          "Use unsafe functions for arrays (more efficient).")
      ; ("--debug", Arg.Set_int Decap.debug_lvl,
          "Sets the value of \"Decap.debug_lvl\".") ]

    (* Function to be run before parsing. *)
    let before_parse_hook : unit -> unit = fun () -> ()

    (* Declaration of grammars for litterals *)
    let char_litteral   : char   grammar = declare_grammar "char_litteral"
    let string_litteral : string grammar = declare_grammar "string_litteral"
    let regexp_litteral : string grammar = declare_grammar "regexp_litteral"

type expression_prio =
  | Seq | If | Aff | Tupl | Disj | Conj | Eq | Append
  | Cons | Sum | Prod | Pow | Opp | App | Dash | Dot | Prefix | Atom

let expression_prios =
  [ Seq ; Aff ; Tupl ; Disj ; Conj ; Eq ; Append
  ; Cons ; Sum ; Prod ; Pow ; Opp ; App ; Dash ; Dot ; Prefix ; Atom]

let next_exp = function
  | Seq -> If
  | If -> Aff
  | Aff -> Tupl
  | Tupl -> Disj
  | Disj -> Conj
  | Conj -> Eq
  | Eq -> Append
  | Append -> Cons
  | Cons -> Sum
  | Sum -> Prod
  | Prod -> Pow
  | Pow -> Opp
  | Opp -> App
  | App -> Dash
  | Dash -> Dot
  | Dot -> Prefix
  | Prefix -> Atom
  | Atom -> Atom

type alm =
    NoMatch | Match | MatchRight | Let | LetRight (* true : if then without else allowed *)

let right_alm = function
  | Match | MatchRight -> Match
  | Let | LetRight -> Let
  | NoMatch -> NoMatch

let left_alm = function
  | Match | MatchRight -> MatchRight
  | Let | LetRight -> LetRight
  | NoMatch -> NoMatch

let allow_match = function
  | Match -> true
  | _ -> false

let allow_let = function
  | Match | Let -> true
  | _ -> false

let string_exp (b,lvl) =
  (match b with NoMatch -> "" | Match -> "m_" | MatchRight -> "mr_"
                              | Let -> "l_" | LetRight -> "lr_"
  ) ^ match lvl with
  | Seq -> "Seq"
  | If -> "If"
  | Aff -> "Aff"
  | Tupl -> "Tupl"
  | Disj -> "Disj"
  | Conj -> "Conj"
  | Eq -> "Eq"
  | Append -> "Append"
  | Cons -> "Cons"
  | Sum -> "Sum"
  | Prod -> "Prod"
  | Pow -> "Pow"
  | Opp -> "Opp"
  | App -> "App"
  | Dash -> "Dash"
  | Dot -> "Dot"
  | Prefix -> "Prefix"
  | Atom -> "Atom"


  let (expression_lvl : (alm * expression_prio) -> expression grammar), set_expression_lvl = grammar_family ~param_to_string:string_exp "expression_lvl"
  let expression = expression_lvl (Match,Seq)
  let structure_item : structure_item list grammar = declare_grammar "structure_item"
  let signature_item : signature_item list grammar = declare_grammar "signature_item"
#if version < 4.03
  type arg_label = string
#endif
  let (parameter : bool -> [`Arg of arg_label * expression option * pattern
           | `Type of string ] grammar), set_parameter = grammar_family "parameter"

  let structure = structure_item

  let parser signature =
      l : {s:signature_item}* -> List.flatten l

  type type_prio = TopType | As | Arr | ProdType | DashType | AppType | AtomType

  let type_prios = [TopType; As; Arr; ProdType; DashType; AppType; AtomType]
  let type_prio_to_string = function
    | TopType -> "TopType" | As -> "As" | Arr -> "Arr" | ProdType -> "ProdType"
    | DashType -> "DashType" | AppType -> "AppType" | AtomType -> "AtomType"
  let next_type_prio = function
    | TopType -> As
    | As -> Arr
    | Arr -> ProdType
    | ProdType -> DashType
    | DashType -> AppType
    | AppType -> AtomType
    | AtomType -> AtomType

  let (typexpr_lvl : type_prio -> core_type grammar), set_typexpr_lvl = grammar_family ~param_to_string:type_prio_to_string "typexpr_lvl"
  let typexpr = typexpr_lvl TopType
  type pattern_prio = TopPat | AsPat | AltPat | TupPat | ConsPat | ConstrPat
                      | AtomPat
  let next_pat_prio = function
    | TopPat -> AsPat
    | AsPat -> AltPat
    | AltPat -> TupPat
    | TupPat -> ConsPat
    | ConsPat -> ConstrPat
    | ConstrPat -> AtomPat
    | AtomPat -> AtomPat
  let (pattern_lvl : pattern_prio -> pattern grammar), set_pattern_lvl = grammar_family "pattern_lvl"
  let pattern = pattern_lvl TopPat

  let let_binding : value_binding list grammar = declare_grammar "let_binding"
  let class_body : class_structure grammar = declare_grammar "class_body"
  let class_expr : class_expr grammar = declare_grammar "class_expr"
  let value_path : Longident.t grammar = declare_grammar "value_path"
  let extra_expressions = ([] : ((alm * expression_prio) -> expression grammar) list)
  let extra_prefix_expressions = ([] : (expression grammar) list)
  let extra_types = ([] : (type_prio -> core_type grammar) list)
  let extra_patterns = ([] : (pattern_prio -> pattern grammar) list)
  let extra_structure = ([] : structure_item list grammar list)
  let extra_signature = ([] : signature_item list grammar list)

  type record_field = Longident.t Asttypes.loc * Parsetree.expression

  let constr_decl_list : constructor_declaration list grammar = declare_grammar "constr_decl_list"
  let field_decl_list : label_declaration list grammar = declare_grammar "field_decl_list"
  let record_list : record_field list grammar = declare_grammar "record_list"
  let match_cases : case list grammar = declare_grammar "match_cases"
  let module_expr : module_expr grammar = declare_grammar "module_expr"
  let module_type : module_type grammar = declare_grammar "module_type"

let parse_string' g e' =
  try
    parse_string g ocaml_blank e'
  with
    e ->
      Printf.eprintf "Error in quotation: %s\n%!" e';
      raise e

(****************************************************************************
 * Gestion of attachment of ocamldoc comments                               *
 ****************************************************************************)

(* no attributes before 4.02 *)
#ifversion >=4.02
let mk_attrib loc s contents =
   (id_loc s Location.none, PStr(
     [loc_str loc (Pstr_eval(exp_string loc contents,[]))
   ]))
#endif

let attach_attrib =
#ifversion < 4.02
  fun ?(local=false) loc acc -> acc
#else
  let tbl_s = Hashtbl.create 31 in
  let tbl_e = Hashtbl.create 31 in
  fun ?(local=false) loc acc ->
    let open Location in
    let open Lexing in
    let rec fn acc res = function
      | [] -> ocamldoc_comments := List.rev acc; res

      | (start,end_,contents as c)::rest ->
	 let start' = loc.loc_start in
	 let loc = locate (fst start) (snd start) (fst end_) (snd end_) in
	 (*Printf.eprintf "start [%d,%d] [%d,...]\n%!"
	   (line_num (fst start)) (line_num (fst end_)) start'.pos_lnum;*)
	 if (start'.pos_lnum >= line_num (fst end_) &&
	       start'.pos_lnum - line_num (fst end_) <= 1 &&
	    (if local then snd start > 0 else snd start = 0))
	 then (
	   fn acc (mk_attrib loc "ocaml.doc" contents::res) rest)
	 else
           fn (c::acc) res rest
    in
    let rec gn acc res = function
      | [] -> ocamldoc_comments := List.rev acc; List.rev res

      | (start,end_,contents as c)::rest ->
	 let end' = loc.loc_end in
	 let loc = locate (fst start) (snd start) (fst end_) (snd end_) in
	 (*Printf.eprintf "end[%d,%d] [...,%d]\n%!"
	   (line_num (fst start)) (line_num (fst end_)) end'.pos_lnum;*)
	 if
	    (line_num (fst start) >= end'.pos_lnum &&
		 line_num (fst start) - end'.pos_lnum  <= 1 &&
	    (if local then snd start > 0 else snd start = 0))
	 then (
	   gn acc (mk_attrib loc "ocaml.doc" contents :: res) rest)
	 else
           gn (c::acc) res rest
    in
    (*    Printf.eprintf "attach_attrib [%d,%d]\n%!" loc.loc_start.pos_lnum  loc.loc_end.pos_lnum;*)
    let l1 =
      try Hashtbl.find tbl_s (loc.loc_start, local)
      with Not_found ->
	let res = fn [] [] !ocamldoc_comments in
	Hashtbl.add tbl_s (loc.loc_start, local) res;
	res
    in
    let l2 =
      try Hashtbl.find tbl_e (loc.loc_end, local)
      with Not_found ->
	let res = gn [] [] !ocamldoc_comments in
	Hashtbl.add tbl_e (loc.loc_end, local) res;
	res
    in
    l1 @ acc @ l2
#endif

#ifversion >= 4.02
let attach_gen build =
  let tbl = Hashtbl.create 31 in
  fun loc ->
    let open Location in
    let open Lexing in
    let rec fn acc res = function
      | [] -> ocamldoc_comments := List.rev acc; res

      | (start,end_,contents as c)::rest ->
	 let start' = loc.loc_start in
	 let loc = locate (fst start) (snd start) (fst end_) (snd end_) in
(*	 Printf.eprintf "sig [%d,%d] [%d,...]\n%!"
	 (line_num (fst start)) (line_num (fst end_)) start'.pos_lnum;*)
	 if line_num (fst end_) < start'.pos_lnum then
	   fn acc (build loc (mk_attrib loc "ocaml.text" contents) :: res) rest
	 else
           fn (c::acc) res rest
    in
    try Hashtbl.find tbl loc.loc_start
    with Not_found ->
      let res = fn [] [] !ocamldoc_comments in
      Hashtbl.add tbl loc.loc_start res;
      res

let attach_sig = attach_gen (fun loc a  -> loc_sig loc (Psig_attribute a))
let attach_str = attach_gen (fun loc a  -> loc_str loc (Pstr_attribute a))
#else
let attach_sig = (fun loc -> [])
let attach_str = (fun loc -> [])
#endif

(****************************************************************************
 * Basic syntactic elements (identifiers and litterals)                      *
 ****************************************************************************)
let union_re l =
  let l = List.map (fun s -> "\\(" ^ s ^ "\\)") l in
  String.concat "\\|" l

let parser arrow_re = ''\(->\)\|\(→\)''

let infix_symb_re prio =
  match prio with
  | Prod -> union_re ["[/%][!$%&*+./:<=>?@^|~-]*";
		      "[*]\\([!$%&+./:<=>?@^|~-][!$%&*+./:<=>?@^|~-]*\\)?";
			"mod\\b"; "land\\b"; "lor\\b"; "lxor\\b"]
  | Sum -> "[+-][!$%&*+./:<=>?@^|~-]*"
  | Append -> "[@^][!$%&*+./:<=>?@^|~-]*"
  | Cons -> "::"
  | Aff -> union_re [":=[!$%&*+./:<=>?@^|~-]*";
		     "<-[!$%&*+./:<=>?@^|~-]*"]
  | Eq -> union_re ["[<][!$%&*+./:<=>?@^|~]?[!$%&*+./:<=>?@^|~-]*";
		    "[&][!$%*+./:<=>?@^|~-][!$%&*+./:<=>?@^|~-]*";
		    "|[!$%&*+./:<=>?@^~-][!$%&*+./:<=>?@^|~-]*";
		    "[=>$][!$%&*+./:<=>?@^|~-]*"; "!="]
  | Conj -> union_re ["[&][&][!$%&*+./:<=>?@^|~-]*"; "[&]"]
  | Disj -> union_re ["or\\b"; "||[!$%&*+./:<=>?@^|~-]*"]
  | Pow -> union_re ["lsl\\b"; "lsr\\b"; "asr\\b"; "[*][*][!$%&*+./:<=>?@^|~-]*"]
  | _ -> assert false

let infix_prios = [ Prod; Sum; Append; Cons; Aff; Eq; Conj; Disj; Pow]

let prefix_symb_re prio =
  match prio with
  | Opp -> union_re ["-[.]?"; "+[.]?"]
  | Prefix ->
     union_re ["[!][!$%&*+./:<=>?@^|~-]*";
	       "[~?][!$%&*+./:<=>?@^|~-]+"]
  | _ -> assert false

let prefix_prios = [ Opp; Prefix ]

let parser infix_symbol prio =
  | "::" when prio = Cons -> "::"
  | sym:RE(infix_symb_re prio) - not_special when prio <> Cons ->
     (if is_reserved_symb sym then give_up ("The infix symbol "^sym^"is reserved..."); sym)

let parser prefix_symbol prio =
    sym:RE(prefix_symb_re prio) - not_special -> (if is_reserved_symb sym || sym = "!=" then give_up ("The prefix symbol "^sym^"is reserved..."); sym)

(****************************************************************************
 * Several flags                                                            *
 ****************************************************************************)

let parser mutable_flag =
  | mutable_kw -> Mutable
  | EMPTY      -> Immutable

let parser private_flag =
  | private_kw -> Private
  | EMPTY      -> Public

let parser virtual_flag =
  | virtual_kw -> Virtual
  | EMPTY      -> Concrete

let parser rec_flag =
  | rec_kw -> Recursive
  | EMPTY  -> Nonrecursive

let parser downto_flag =
  | to_kw     -> Upto
  | downto_kw -> Downto

let entry_points : (string * entry_point) list =
   [ ".mli", Interface      (signature, ocaml_blank)
   ;  ".ml", Implementation (structure, ocaml_blank) ]
end

module type Extension = module type of Initial

module type FExt = functor (E:Extension) -> Extension

include Initial

let start_pos loc =
  loc.Location.loc_start

let end_pos loc =
  loc.Location.loc_end


