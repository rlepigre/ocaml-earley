open Input
open Earley
open Asttypes
open Parsetree
open Pa_ast
open Pa_lexing
type entry =  
  | FromExt
  | Impl
  | Intf 
let entry: entry ref = ref FromExt
let fast: bool ref = ref false
let file: string option ref = ref None
let ascii: bool ref = ref false
let print_location ch { Location.loc_start = s; Location.loc_end = e } =
  let open Lexing in
    Printf.fprintf ch "Position %d:%d to %d:%d%!" s.pos_lnum
      (s.pos_cnum - s.pos_bol) e.pos_lnum (e.pos_cnum - e.pos_bol)
let string_location { Location.loc_start = s; Location.loc_end = e } =
  let open Lexing in
    Printf.sprintf "Position %d:%d to %d:%d%!" s.pos_lnum
      (s.pos_cnum - s.pos_bol) e.pos_lnum (e.pos_cnum - e.pos_bol)
let lexing_position str pos =
  let loff = line_offset str in
  let open Lexing in
    {
      pos_fname = (filename str);
      pos_lnum = (line_num str);
      pos_cnum = (loff + pos);
      pos_bol = loff
    }
let locate str pos str' pos' =
  let open Lexing in
    let s = lexing_position str pos in
    let e = lexing_position str' pos' in
    let open Location in { loc_start = s; loc_end = e; loc_ghost = false }
type entry_point =  
  | Implementation of Parsetree.structure_item list grammar* blank
  | Interface of Parsetree.signature_item list grammar* blank 
module Initial =
  struct
    let spec: (Arg.key* Arg.spec* Arg.doc) list =
      [("--ascii", (Arg.Set ascii),
         "Output ASCII text instead of serialized AST.");
      ("--impl", (Arg.Unit ((fun ()  -> entry := Impl))),
        "Treat file as an implementation.");
      ("--intf", (Arg.Unit ((fun ()  -> entry := Intf))),
        "Treat file as an interface.");
      ("--unsafe", (Arg.Set fast),
        "Use unsafe functions for arrays (more efficient).");
      ("--position-from-parser", (Arg.Set Quote.quote_parser_position),
        "Report position from quotation in parser (usefull to debug quotation).");
      ("--debug", (Arg.Set_int Earley.debug_lvl),
        "Sets the value of \"Earley.debug_lvl\".")]
    let before_parse_hook: unit -> unit = fun ()  -> ()
    let char_litteral: char grammar = declare_grammar "char_litteral"
    let string_litteral: string grammar = declare_grammar "string_litteral"
    let regexp_litteral: string grammar = declare_grammar "regexp_litteral"
    type expression_prio =  
      | Seq
      | If
      | Aff
      | Tupl
      | Disj
      | Conj
      | Eq
      | Append
      | Cons
      | Sum
      | Prod
      | Pow
      | Opp
      | App
      | Dash
      | Dot
      | Prefix
      | Atom 
    let expression_prios =
      [Seq;
      Aff;
      Tupl;
      Disj;
      Conj;
      Eq;
      Append;
      Cons;
      Sum;
      Prod;
      Pow;
      Opp;
      App;
      Dash;
      Dot;
      Prefix;
      Atom]
    let next_exp =
      function
      | Seq  -> If
      | If  -> Aff
      | Aff  -> Tupl
      | Tupl  -> Disj
      | Disj  -> Conj
      | Conj  -> Eq
      | Eq  -> Append
      | Append  -> Cons
      | Cons  -> Sum
      | Sum  -> Prod
      | Prod  -> Pow
      | Pow  -> Opp
      | Opp  -> App
      | App  -> Dash
      | Dash  -> Dot
      | Dot  -> Prefix
      | Prefix  -> Atom
      | Atom  -> Atom
    type alm =  
      | NoMatch
      | Match
      | MatchRight
      | Let
      | LetRight 
    let right_alm =
      function
      | Match |MatchRight  -> Match
      | Let |LetRight  -> Let
      | NoMatch  -> NoMatch
    let left_alm =
      function
      | Match |MatchRight  -> MatchRight
      | Let |LetRight  -> LetRight
      | NoMatch  -> NoMatch
    let allow_match = function | Match  -> true | _ -> false
    let allow_let = function | Match |Let  -> true | _ -> false
    let string_exp (b,lvl) =
      (match b with
       | NoMatch  -> ""
       | Match  -> "m_"
       | MatchRight  -> "mr_"
       | Let  -> "l_"
       | LetRight  -> "lr_") ^
        (match lvl with
         | Seq  -> "Seq"
         | If  -> "If"
         | Aff  -> "Aff"
         | Tupl  -> "Tupl"
         | Disj  -> "Disj"
         | Conj  -> "Conj"
         | Eq  -> "Eq"
         | Append  -> "Append"
         | Cons  -> "Cons"
         | Sum  -> "Sum"
         | Prod  -> "Prod"
         | Pow  -> "Pow"
         | Opp  -> "Opp"
         | App  -> "App"
         | Dash  -> "Dash"
         | Dot  -> "Dot"
         | Prefix  -> "Prefix"
         | Atom  -> "Atom")
    let ((expression_lvl : (alm* expression_prio) -> expression grammar),set_expression_lvl)
      = grammar_family ~param_to_string:string_exp "expression_lvl"
    let expression = expression_lvl (Match, Seq)
    let structure_item: structure_item list grammar =
      declare_grammar "structure_item"
    let signature_item: signature_item list grammar =
      declare_grammar "signature_item"
    type arg_label = string 
    let ((parameter :
           bool ->
             [ `Arg of (arg_label* expression option* pattern)
             | `Type of string] grammar),set_parameter)
      = grammar_family "parameter"
    let structure = structure_item
    let signature = Earley.declare_grammar "signature"
    let _ =
      Earley.set_grammar signature
        (Earley.apply (fun l  -> List.flatten l)
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  y  -> x :: y) signature_item))))
    type type_prio =  
      | TopType
      | As
      | Arr
      | ProdType
      | DashType
      | AppType
      | AtomType 
    let type_prios =
      [TopType; As; Arr; ProdType; DashType; AppType; AtomType]
    let type_prio_to_string =
      function
      | TopType  -> "TopType"
      | As  -> "As"
      | Arr  -> "Arr"
      | ProdType  -> "ProdType"
      | DashType  -> "DashType"
      | AppType  -> "AppType"
      | AtomType  -> "AtomType"
    let next_type_prio =
      function
      | TopType  -> As
      | As  -> Arr
      | Arr  -> ProdType
      | ProdType  -> DashType
      | DashType  -> AppType
      | AppType  -> AtomType
      | AtomType  -> AtomType
    let ((typexpr_lvl : type_prio -> core_type grammar),set_typexpr_lvl) =
      grammar_family ~param_to_string:type_prio_to_string "typexpr_lvl"
    let typexpr = typexpr_lvl TopType
    type pattern_prio =  
      | AltPat
      | TupPat
      | ConsPat
      | ConstrPat
      | AtomPat 
    let topPat = AltPat
    let next_pat_prio =
      function
      | AltPat  -> TupPat
      | TupPat  -> ConsPat
      | ConsPat  -> ConstrPat
      | ConstrPat  -> AtomPat
      | AtomPat  -> AtomPat
    let ((pattern_lvl : (bool* pattern_prio) -> pattern grammar),set_pattern_lvl)
      = grammar_family "pattern_lvl"
    let pattern = pattern_lvl (true, topPat)
    let let_binding: value_binding list grammar =
      declare_grammar "let_binding"
    let class_body: class_structure grammar = declare_grammar "class_body"
    let class_expr: class_expr grammar = declare_grammar "class_expr"
    let value_path: Longident.t grammar = declare_grammar "value_path"
    let extra_expressions:
      ((alm* expression_prio) -> expression grammar) list = []
    let extra_prefix_expressions: expression grammar list = []
    let extra_types: (type_prio -> core_type grammar) list = []
    let extra_patterns: ((bool* pattern_prio) -> pattern grammar) list = []
    let extra_structure: structure_item list grammar list = []
    let extra_signature: signature_item list grammar list = []
    type record_field = (Longident.t Asttypes.loc* Parsetree.expression) 
    let constr_decl_list: constructor_declaration list grammar =
      declare_grammar "constr_decl_list"
    let field_decl_list: label_declaration list grammar =
      declare_grammar "field_decl_list"
    let record_list: record_field list grammar =
      declare_grammar "record_list"
    let match_cases: case list grammar = declare_grammar "match_cases"
    let module_expr: module_expr grammar = declare_grammar "module_expr"
    let module_type: module_type grammar = declare_grammar "module_type"
    let parse_string' g e' =
      try parse_string g ocaml_blank e'
      with | e -> (Printf.eprintf "Error in quotation: %s\n%!" e'; raise e)
    let attach_attrib ?(local= false)  loc acc = acc
    let attach_sig loc = []
    let attach_str loc = []
    let union_re l =
      let l = List.map (fun s  -> "\\(" ^ (s ^ "\\)")) l in
      String.concat "\\|" l
    let arrow_re = Earley.declare_grammar "arrow_re"
    let _ =
      Earley.set_grammar arrow_re
        (EarleyStr.regexp ~name:"\\\\(->\\\\)\\\\|\\\\(\\226\\134\\146\\\\)"
           "\\(->\\)\\|\\(\226\134\146\\)" (fun groupe  -> groupe 0))
    let infix_symb_re prio =
      match prio with
      | Prod  ->
          union_re
            ["[/%][!$%&*+./:<=>?@^|~-]*";
            "[*]\\([!$%&+./:<=>?@^|~-][!$%&*+./:<=>?@^|~-]*\\)?";
            "mod\\b";
            "land\\b";
            "lor\\b";
            "lxor\\b"]
      | Sum  -> "[+-][!$%&*+./:<=>?@^|~-]*"
      | Append  -> "[@^][!$%&*+./:<=>?@^|~-]*"
      | Cons  -> "::"
      | Aff  ->
          union_re [":=[!$%&*+./:<=>?@^|~-]*"; "<-[!$%&*+./:<=>?@^|~-]*"]
      | Eq  ->
          union_re
            ["[<][!$%&*+./:<=>?@^|~]?[!$%&*+./:<=>?@^|~-]*";
            "[&][!$%*+./:<=>?@^|~-][!$%&*+./:<=>?@^|~-]*";
            "|[!$%&*+./:<=>?@^~-][!$%&*+./:<=>?@^|~-]*";
            "[=>$][!$%&*+./:<=>?@^|~-]*";
            "!="]
      | Conj  -> union_re ["[&][&][!$%&*+./:<=>?@^|~-]*"; "[&]"]
      | Disj  -> union_re ["or\\b"; "||[!$%&*+./:<=>?@^|~-]*"]
      | Pow  ->
          union_re
            ["lsl\\b"; "lsr\\b"; "asr\\b"; "[*][*][!$%&*+./:<=>?@^|~-]*"]
      | _ -> assert false
    let infix_prios = [Prod; Sum; Append; Cons; Aff; Eq; Conj; Disj; Pow]
    let prefix_symb_re prio =
      match prio with
      | Opp  -> union_re ["-[.]?"; "+[.]?"]
      | Prefix  ->
          union_re ["[!][!$%&*+./:<=>?@^|~-]*"; "[~?][!$%&*+./:<=>?@^|~-]+"]
      | _ -> assert false
    let prefix_prios = [Opp; Prefix]
    let (infix_symbol,infix_symbol__set__grammar) =
      Earley.grammar_family "infix_symbol"
    let _ =
      infix_symbol__set__grammar
        (fun prio  ->
           Earley.alternatives
             (let y =
                let y = [] in
                if prio <> Cons
                then
                  (Earley.sequence
                     (Earley.ignore_next_blank
                        (EarleyStr.regexp (infix_symb_re prio)
                           (fun groupe  -> groupe 0))) not_special
                     (fun sym  _default_0  ->
                        if is_reserved_symb sym then give_up (); sym))
                  :: y
                else y in
              if prio = Cons
              then (Earley.apply (fun _  -> "::") (Earley.string "::" "::"))
                :: y
              else y))
    let (prefix_symbol,prefix_symbol__set__grammar) =
      Earley.grammar_family "prefix_symbol"
    let _ =
      prefix_symbol__set__grammar
        (fun prio  ->
           Earley.sequence
             (Earley.ignore_next_blank
                (EarleyStr.regexp (prefix_symb_re prio)
                   (fun groupe  -> groupe 0))) not_special
             (fun sym  _default_0  ->
                if (is_reserved_symb sym) || (sym = "!=") then give_up ();
                sym))
    let mutable_flag = Earley.declare_grammar "mutable_flag"
    let _ =
      Earley.set_grammar mutable_flag
        (Earley.alternatives
           [Earley.apply (fun _default_0  -> Mutable) mutable_kw;
           Earley.apply (fun _  -> Immutable) (Earley.empty ())])
    let private_flag = Earley.declare_grammar "private_flag"
    let _ =
      Earley.set_grammar private_flag
        (Earley.alternatives
           [Earley.apply (fun _default_0  -> Private) private_kw;
           Earley.apply (fun _  -> Public) (Earley.empty ())])
    let virtual_flag = Earley.declare_grammar "virtual_flag"
    let _ =
      Earley.set_grammar virtual_flag
        (Earley.alternatives
           [Earley.apply (fun _default_0  -> Virtual) virtual_kw;
           Earley.apply (fun _  -> Concrete) (Earley.empty ())])
    let rec_flag = Earley.declare_grammar "rec_flag"
    let _ =
      Earley.set_grammar rec_flag
        (Earley.alternatives
           [Earley.apply (fun _default_0  -> Recursive) rec_kw;
           Earley.apply (fun _  -> Nonrecursive) (Earley.empty ())])
    let downto_flag = Earley.declare_grammar "downto_flag"
    let _ =
      Earley.set_grammar downto_flag
        (Earley.alternatives
           [Earley.apply (fun _default_0  -> Upto) to_kw;
           Earley.apply (fun _default_0  -> Downto) downto_kw])
    let entry_points: (string* entry_point) list =
      [(".mli", (Interface (signature, ocaml_blank)));
      (".ml", (Implementation (structure, ocaml_blank)))]
  end
module type Extension = module type of Initial
module type FExt = functor (E : Extension) -> Extension
include Initial
let start_pos loc = loc.Location.loc_start
let end_pos loc = loc.Location.loc_end
