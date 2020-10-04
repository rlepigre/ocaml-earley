(* Copyright 2016-2020 Christophe Raffalli & Rodolphe Lepigre. *)

open Earley_core
open Input
open Earley
open Asttypes
open Parsetree
open Pa_lexing
open Ast_helper

let print_location ch loc =
  let (s, e) = Location.(loc.loc_start, loc.loc_end) in
  Printf.fprintf ch "Position %d:%d to %d:%d%!"
    s.pos_lnum (s.pos_cnum - s.pos_bol)
    e.pos_lnum (e.pos_cnum - e.pos_bol)

let lexing_position str pos =
  let pos_fname = filename str in
  let pos_lnum  = line_num str in
  let pos_bol   = line_offset str in
  let pos_cnum  = pos_bol + pos in
  Lexing.{pos_fname; pos_lnum; pos_cnum; pos_bol}

(* Location function. *)
let locate str1 pos1 str2 pos2 =
  let loc_start = lexing_position str1 pos1 in
  let loc_end   = lexing_position str2 pos2 in
  Location.{loc_start; loc_end; loc_ghost = false}

#define LOCATE locate

let debug_attach = ref false

type expression_prio =
  | Seq | If | Aff | Tupl | Disj | Conj | Eq | Append
  | Cons | Sum | Prod | Pow | Opp | App | Dash | Dot | Prefix | Atom

let expression_prios =
  [Seq; Aff; Tupl; Disj; Conj; Eq; Append; Cons; Sum; Prod; Pow; Opp; App;
   Dash; Dot; Prefix; Atom]

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
    NoMatch | Match | Let

let allow_match = function
  | Match -> true
  | _ -> false

let allow_let = function
  | Match | Let -> true
  | _ -> false

let string_exp (b,lvl) =
  (match b with NoMatch -> "" | Match -> "m_" | Let -> "l_") ^
  (match lvl with
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
  | Atom -> "Atom")


let ((expression_lvl : alm * expression_prio -> expression grammar)
    , set_expression_lvl)
  = grammar_family ~param_to_string:string_exp "expression_lvl"
let expression = expression_lvl (Match, Seq)
let structure_item : structure_item list grammar
  = declare_grammar "structure_item"
let signature_item : signature_item list grammar
  = declare_grammar "signature_item"
let (parameter : bool -> [`Arg of arg_label * expression option * pattern
                         | `Type of string Location.loc ]
                           grammar), set_parameter = grammar_family "parameter"

let structure = structure_item

let parser signature =
    l : {s:signature_item}* -> List.flatten l

type type_prio = TopType | As | Arr | ProdType | DashType | AppType | AtomType

let type_prios = [TopType; As; Arr; ProdType; DashType; AppType; AtomType]
let type_prio_to_string (_, lvl) = match lvl with
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

let (typexpr_lvl_raw : (bool * type_prio) -> core_type grammar), set_typexpr_lvl =
  grammar_prio ~param_to_string:type_prio_to_string "typexpr_lvl"
let typexpr_lvl lvl = typexpr_lvl_raw (true, lvl)
let typexpr_nopar = typexpr_lvl_raw (false, TopType)
let typexpr = typexpr_lvl TopType
type pattern_prio = AltPat | TupPat | ConsPat | ConstrPat | AtomPat
let topPat = AltPat
let pat_prio_to_string (_, lvl) = match lvl with
  | AltPat -> "AltPat" | TupPat -> "TupPat" | ConsPat -> "ConsPat"
  | ConstrPat -> "ConstrPat" | AtomPat -> "AtomPat"
let next_pat_prio = function
  | AltPat -> TupPat
  | TupPat -> ConsPat
  | ConsPat -> ConstrPat
  | ConstrPat -> AtomPat
  | AtomPat -> assert false
let (pattern_lvl : bool * pattern_prio -> pattern grammar), set_pattern_lvl =
  grammar_prio ~param_to_string:pat_prio_to_string "pattern_lvl"
let pattern = pattern_lvl (true,topPat)

let let_binding : value_binding list grammar = declare_grammar "let_binding"
let class_body : class_structure grammar = declare_grammar "class_body"
let class_expr : class_expr grammar = declare_grammar "class_expr"
let value_path : Longident.t grammar = declare_grammar "value_path"

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

let mk_attrib loc txt contents =
  let str = Const.string contents in
  ({txt; loc = Location.none}, PStr [Str.eval ~loc (Exp.constant ~loc str)])


let attach_attrib =
  let tbl_s = Hashtbl.create 31 in
  let tbl_e = Hashtbl.create 31 in
  let attach_attrib loc (acc : attribute list)  : attribute list =
    let open Location in
    let open Lexing in
    if !debug_attach then Printf.eprintf "enter attach\n%!";
    let rec fn acc res = function
      | [] -> res

      | (start,end_,contents,_ as c)::rest ->
         let start' = loc.loc_start in
         let lend = line_num (fst end_) in
         let loc = locate (fst start) (snd start) (fst end_) (snd end_) in
         if !debug_attach then Printf.eprintf "start [%d,%d] [%d,...]\n%!"
                        (line_num (fst start)) lend start'.pos_lnum;
         (** Attach comments before only if on the previous line*)
         if start'.pos_lnum > lend && start'.pos_lnum - lend <= 1
         then (
           if !debug_attach then Printf.eprintf "attach backward %s\n%!" contents;
           ocamldoc_comments := List.rev_append acc rest;
           if contents <> "" then mk_attrib loc "ocaml.doc" contents::res else res)
         else
           fn (c::acc) res rest
    in
    let rec gn acc res = function
      | [] -> List.rev res

      | (start,end_,contents,lstart as c)::rest ->
         let end' = loc.loc_end in
         let loc = locate (fst start) (snd start) (fst end_) (snd end_) in
         if !debug_attach then Printf.eprintf "end[%d,%d] [...,%d]\n%!"
           lstart (line_num (fst end_)) end'.pos_lnum;
         if lstart >= end'.pos_lnum && lstart - end'.pos_lnum  <= 1
         then (
           if !debug_attach then Printf.eprintf "attach forward %s\n%!" contents;
           ocamldoc_comments := List.rev_append rest acc;
           if contents <> "" then mk_attrib loc "ocaml.doc" contents :: res else res)
         else
           gn (c::acc) res rest
    in
    (*    Printf.eprintf "attach_attrib [%d,%d]\n%!" loc.loc_start.pos_lnum  loc.loc_end.pos_lnum;*)
    let l2 =
      try Hashtbl.find tbl_e (loc.loc_start, loc.loc_end)
      with Not_found ->
        let res = gn [] [] (List.rev !ocamldoc_comments) in
        Hashtbl.add tbl_e (loc.loc_start, loc.loc_end) res;
        res
    in
    let l1 =
      try Hashtbl.find tbl_s loc.loc_start
      with Not_found ->
        let res = fn [] [] !ocamldoc_comments in
        Hashtbl.add tbl_s loc.loc_start res;
        res
    in
    let l1 = List.map (fun (s,pl) -> Attr.mk s pl) l1 in
    let l2 = List.map (fun (s,pl) -> Attr.mk s pl) l2 in
    (l1 @ acc @ l2)
  in
  attach_attrib

let attach_gen build =
  let tbl = Hashtbl.create 31 in
  fun loc ->
    let open Location in
    let open Lexing in
    let rec fn acc res = function
      | [] -> ocamldoc_comments := List.rev acc; res

      | (start,end_,contents,_ as c)::rest ->
         let start' = loc.loc_start in
         let loc = locate (fst start) (snd start) (fst end_) (snd end_) in
         if !debug_attach then Printf.eprintf "sig/str [%d,%d] [%d,...]\n%!"
           (line_num (fst start)) (line_num (fst end_)) start'.pos_lnum;
           if line_num (fst end_) < start'.pos_lnum - 1 then
             begin
               if !debug_attach then
                 Printf.eprintf "attach ocaml.text %s\n%!" contents;
               fn acc (build loc (mk_attrib loc "ocaml.text" contents)
                       :: res) rest
             end
         else
           fn (c::acc) res rest
    in
    if !debug_attach then Printf.eprintf "enter attach sig/str [%d,...] %d\n%!"
                     loc.loc_start.pos_lnum (List.length !ocamldoc_comments);
    try Hashtbl.find tbl loc.loc_start
    with Not_found ->
      let res = fn [] [] !ocamldoc_comments in
      Hashtbl.add tbl loc.loc_start res;
      res

let attach_sig =
  attach_gen (fun loc (str,pl)  -> Sig.attribute ~loc (Attr.mk ~loc str pl))

let attach_str =
  attach_gen (fun loc (str,pl)  -> Str.attribute ~loc (Attr.mk ~loc str pl))

(****************************************************************************
 * Basic syntactic elements (identifiers and litterals)                      *
 ****************************************************************************)

let union_re l =
  String.concat "\\|" (List.map (fun s -> "\\(" ^ s ^ "\\)") l)

let infix_symb_re prio =
  match prio with
  | Prod   -> union_re ["[/%][!$%&*+./:<=>?@^|~-]*";
                        "[*]\\([!$%&+./:<=>?@^|~-][!$%&*+./:<=>?@^|~-]*\\)?";
                        "mod\\b"; "land\\b"; "lor\\b"; "lxor\\b"]
  | Sum    -> "[+-][!$%&*+./:<=>?@^|~-]*"
  | Append -> "[@^][!$%&*+./:<=>?@^|~-]*"
  | Cons   -> "::"
  | Aff    -> union_re [":=[!$%&*+./:<=>?@^|~-]*";
                        "<-[!$%&*+./:<=>?@^|~-]*"]
  | Eq     -> union_re ["[<][!$%&*+./:<=>?@^|~]?[!$%&*+./:<=>?@^|~-]*";
                        "[&][!$%*+./:<=>?@^|~-][!$%&*+./:<=>?@^|~-]*";
                        "|[!$%&*+./:<=>?@^~-][!$%&*+./:<=>?@^|~-]*";
                        "[=>$][!$%&*+./:<=>?@^|~-]*"; "!="]
  | Conj   -> union_re ["[&][&][!$%&*+./:<=>?@^|~-]*"; "[&]"]
  | Disj   -> union_re ["or\\b"; "||[!$%&*+./:<=>?@^|~-]*"]
  | Pow    -> union_re ["lsl\\b"; "lsr\\b"; "asr\\b";
                        "[*][*][!$%&*+./:<=>?@^|~-]*"]
  | _      -> assert false

let infix_prios = [ Prod; Sum; Append; Cons; Aff; Eq; Conj; Disj; Pow]

let prefix_symb_re prio =
  match prio with
  | Opp    -> union_re ["-[.]?"; "+[.]?"]
  | Prefix -> union_re ["[!][!$%&*+./:<=>?@^|~-]*";
                        "[~?][!$%&*+./:<=>?@^|~-]+"]
  | _      -> assert false

let parser infix_symbol prio =
  | "::"                                   when prio =  Cons -> "::"
  | sym:RE(infix_symb_re prio) not_special when prio <> Cons ->
      if is_reserved_symb sym then give_up () else sym

let parser prefix_symbol prio =
  | sym:RE(prefix_symb_re prio) not_special ->
      if is_reserved_symb sym || sym = "!=" then give_up () else sym

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
