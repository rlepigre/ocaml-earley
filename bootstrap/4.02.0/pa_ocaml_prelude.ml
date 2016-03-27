open Input
open Decap
open Charset
open Asttypes
open Parsetree
open Longident
open Pa_ast
open Pa_lexing
let fast = ref false
let file: string option ref = ref None
let ascii = ref false
let in_ocamldep = ref false
type entry =
  | FromExt
  | Impl
  | Intf
let entry = ref FromExt
let spec =
  ref
    [("--ascii", (Arg.Set ascii),
       "output ascii ast instead of serialized ast");
    ("--impl", (Arg.Unit ((fun ()  -> entry := Impl))),
      "treat file as an implementation");
    ("--intf", (Arg.Unit ((fun ()  -> entry := Intf))),
      "treat file as an interface");
    ("--unsafe", (Arg.Set fast), "use unsafe function for arrays");
    ("--ocamldep", (Arg.Set in_ocamldep),
      "set a flag to inform parser that we are computing dependencies");
    ("--debug", (Arg.Set_int Decap.debug_lvl), "set decap debug_lvl")]
let extend_cl_args l = spec := ((!spec) @ l)
let ghost loc = let open Location in { loc with loc_ghost = true }
let no_ghost loc = let open Location in { loc with loc_ghost = false }
let de_ghost e = loc_expr (no_ghost e.pexp_loc) e.pexp_desc
let start_pos loc = loc.Location.loc_start
let end_pos loc = loc.Location.loc_end
let locate str pos str' pos' =
  let open Lexing in
    let s = Input.lexing_position str pos in
    let e = Input.lexing_position str' pos' in
    let open Location in { loc_start = s; loc_end = e; loc_ghost = false }
let rec merge =
  function
  | [] -> assert false
  | loc::[] -> loc
  | l1::_ as ls ->
      let ls = List.rev ls in
      let rec fn =
        function
        | [] -> assert false
        | loc::[] -> loc
        | l2::ls when let open Location in l2.loc_start = l2.loc_end -> fn ls
        | l2::ls ->
            let open Location in
              {
                loc_start = (l1.loc_start);
                loc_end = (l2.loc_end);
                loc_ghost = (l1.loc_ghost && l2.loc_ghost)
              } in
      fn ls
let merge2 l1 l2 =
  let open Location in
    {
      loc_start = (l1.loc_start);
      loc_end = (l2.loc_end);
      loc_ghost = (l1.loc_ghost && l2.loc_ghost)
    }
type entry_point =
  | Implementation of Parsetree.structure_item list Decap.grammar* blank
  | Interface of Parsetree.signature_item list Decap.grammar* blank
module Initial =
  struct
    let before_parse_hook () = ()
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
    let signature = Decap.declare_grammar "signature"
    let _ =
      Decap.set_grammar signature
        (Decap.apply (fun l  -> List.flatten l)
           (Decap.apply List.rev
              (Decap.fixpoint []
                 (Decap.apply (fun x  -> fun l  -> x :: l) signature_item))))
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
      | TopPat
      | AsPat
      | AltPat
      | TupPat
      | ConsPat
      | ConstrPat
      | AtomPat
    let next_pat_prio =
      function
      | TopPat  -> AsPat
      | AsPat  -> AltPat
      | AltPat  -> TupPat
      | TupPat  -> ConsPat
      | ConsPat  -> ConstrPat
      | ConstrPat  -> AtomPat
      | AtomPat  -> AtomPat
    let ((pattern_lvl : pattern_prio -> pattern grammar),set_pattern_lvl) =
      grammar_family "pattern_lvl"
    let pattern = pattern_lvl TopPat
    let let_binding: value_binding list grammar =
      declare_grammar "let_binding"
    let class_body: class_structure grammar = declare_grammar "class_body"
    let class_expr: class_expr grammar = declare_grammar "class_expr"
    let value_path: Longident.t grammar = declare_grammar "value_path"
    let extra_expressions:
      ((alm* expression_prio) -> expression grammar) list = []
    let extra_prefix_expressions: expression grammar list = []
    let extra_types: (type_prio -> core_type grammar) list = []
    let extra_patterns: (pattern_prio -> pattern grammar) list = []
    let extra_structure: structure_item list grammar list = []
    let extra_signature: signature_item list grammar list = []
    let constructor_declaration ?(attributes= [])  _loc name args res =
      {
        pcd_name = name;
        pcd_args = args;
        pcd_res = res;
        pcd_attributes = attributes;
        pcd_loc = _loc
      }
    let label_declaration _loc name mut ty =
      {
        pld_name = name;
        pld_mutable = mut;
        pld_type = ty;
        pld_attributes = [];
        pld_loc = _loc
      }
    let params_map _loc params =
      let fn (name,var) =
        match name with
        | None  -> ((loc_typ _loc Ptyp_any), var)
        | Some name -> ((loc_typ name.loc (Ptyp_var (name.txt))), var) in
      List.map fn params
    let type_declaration ?(attributes= [])  _loc name params cstrs kind priv
      manifest =
      let params = params_map _loc params in
      {
        ptype_name = name;
        ptype_params = params;
        ptype_cstrs = cstrs;
        ptype_kind = kind;
        ptype_private = priv;
        ptype_manifest = manifest;
        ptype_attributes = attributes;
        ptype_loc = _loc
      }
    let class_type_declaration ?(attributes= [])  _loc' _loc name params virt
      expr =
      let params = params_map _loc' params in
      {
        pci_params = params;
        pci_virt = virt;
        pci_name = name;
        pci_expr = expr;
        pci_attributes = attributes;
        pci_loc = _loc
      }
    let pstr_eval e = Pstr_eval (e, [])
    let psig_value ?(attributes= [])  _loc name ty prim =
      Psig_value
        {
          pval_name = name;
          pval_type = ty;
          pval_prim = prim;
          pval_attributes = attributes;
          pval_loc = _loc
        }
    let value_binding ?(attributes= [])  _loc pat expr =
      {
        pvb_pat = pat;
        pvb_expr = expr;
        pvb_attributes = attributes;
        pvb_loc = _loc
      }
    let module_binding _loc name mt me =
      let me =
        match mt with
        | None  -> me
        | Some mt -> mexpr_loc _loc (Pmod_constraint (me, mt)) in
      { pmb_name = name; pmb_expr = me; pmb_attributes = []; pmb_loc = _loc }
    let module_declaration ?(attributes= [])  _loc name mt =
      {
        pmd_name = name;
        pmd_type = mt;
        pmd_attributes = attributes;
        pmd_loc = _loc
      }
    let ppat_construct (a,b) = Ppat_construct (a, b)
    let pexp_constraint (a,b) = Pexp_constraint (a, b)
    let pexp_coerce (a,b,c) = Pexp_coerce (a, b, c)
    let pexp_assertfalse _loc =
      Pexp_assert
        (loc_expr _loc
           (pexp_construct ({ txt = (Lident "false"); loc = _loc }, None)))
    let make_case pat expr guard =
      { pc_lhs = pat; pc_rhs = expr; pc_guard = guard }
    let pexp_function cases = Pexp_function cases
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
    let localise _loc e =
      let len = String.length e in
      if (len = 0) || ((e.[0]) = '#')
      then e
      else
        (let cols =
           let n =
             let open Location in
               let open Lexing in
                 (_loc.loc_start).pos_cnum - (_loc.loc_start).pos_bol in
           String.make (n + 1) ' ' in
         ((let open Location in
             let open Lexing in
               Printf.sprintf "#%d %S\n%s" ((_loc.loc_start).pos_lnum - 1)
                 (_loc.loc_start).pos_fname) cols)
           ^ e)
    let loc_none =
      let loc =
        let open Lexing in
          { pos_fname = "none"; pos_lnum = 1; pos_bol = 0; pos_cnum = (-1) } in
      let open Location in
        { loc_start = loc; loc_end = loc; loc_ghost = true }
    let parse_string' g e' =
      try parse_string g ocaml_blank e'
      with | e -> (Printf.eprintf "Error in quotation: %s\n%!" e'; raise e)
    let mk_attrib loc s contents =
      ((id_loc s Location.none),
        (PStr [loc_str loc (Pstr_eval ((exp_string loc contents), []))]))
    let attach_attrib =
      let tbl = Hashtbl.create 31 in
      fun ?(delta= 1)  ->
        fun loc  ->
          fun acc  ->
            let open Location in
              let open Lexing in
                let rec fn acc res =
                  function
                  | [] -> (ocamldoc_comments := (List.rev acc); res)
                  | ((start,end_,contents) as c)::rest ->
                      let start' = loc.loc_start in
                      let end' = loc.loc_end in
                      let loc =
                        locate (fst start) (snd start) (fst end_) (snd end_) in
                      if
                        (start'.pos_lnum >= (line_num (fst end_))) &&
                          ((start'.pos_lnum - (line_num (fst end_))) <= delta)
                      then
                        fn acc ((mk_attrib loc "ocaml.doc" contents) :: res)
                          rest
                      else
                        if
                          ((line_num (fst start)) >= end'.pos_lnum) &&
                            (((line_num (fst start)) - end'.pos_lnum) <=
                               delta)
                        then
                          fn acc (res @ [mk_attrib loc "ocaml.doc" contents])
                            rest
                        else fn (c :: acc) res rest in
                try Hashtbl.find tbl loc
                with
                | Not_found  ->
                    let res = fn [] acc (!ocamldoc_comments) in
                    (Hashtbl.add tbl loc res; res)
    let attach_gen build =
      let tbl = Hashtbl.create 31 in
      fun loc  ->
        let open Location in
          let open Lexing in
            let rec fn acc res =
              function
              | [] -> (ocamldoc_comments := (List.rev acc); res)
              | ((start,end_,contents) as c)::rest ->
                  let start' = loc.loc_start in
                  let loc =
                    locate (fst start) (snd start) (fst end_) (snd end_) in
                  if (line_num (fst end_)) < start'.pos_lnum
                  then
                    fn acc ((build loc (mk_attrib loc "ocaml.text" contents))
                      :: res) rest
                  else fn (c :: acc) res rest in
            try Hashtbl.find tbl loc.loc_start
            with
            | Not_found  ->
                let res = fn [] [] (!ocamldoc_comments) in
                (Hashtbl.add tbl loc.loc_start res; res)
    let attach_sig =
      attach_gen (fun loc  -> fun a  -> loc_sig loc (Psig_attribute a))
    let attach_str =
      attach_gen (fun loc  -> fun a  -> loc_str loc (Pstr_attribute a))
    let union_re l =
      let l = List.map (fun s  -> "\\(" ^ (s ^ "\\)")) l in
      String.concat "\\|" l
    let arrow_re = Decap.declare_grammar "arrow_re"
    let _ =
      Decap.set_grammar arrow_re
        (Decap.regexp ~name:"\\(->\\)\\|\\(\226\134\146\\)"
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
      Decap.grammar_family "infix_symbol"
    let _ =
      infix_symbol__set__grammar
        (fun prio  ->
           Decap.alternatives
             (let y =
                let y = [] in
                if prio <> Cons
                then
                  (Decap.sequence
                     (Decap.ignore_next_blank
                        (Decap.regexp (infix_symb_re prio)
                           (fun groupe  -> groupe 0))) not_special
                     (fun sym  ->
                        fun _default_0  ->
                          if is_reserved_symb sym
                          then
                            give_up
                              ("The infix symbol " ^ (sym ^ "is reserved..."));
                          sym))
                  :: y
                else y in
              if prio = Cons
              then (Decap.apply (fun _  -> "::") (Decap.string "::" "::")) ::
                y
              else y))
    let (prefix_symbol,prefix_symbol__set__grammar) =
      Decap.grammar_family "prefix_symbol"
    let _ =
      prefix_symbol__set__grammar
        (fun prio  ->
           Decap.sequence
             (Decap.ignore_next_blank
                (Decap.regexp (prefix_symb_re prio) (fun groupe  -> groupe 0)))
             not_special
             (fun sym  ->
                fun _default_0  ->
                  if (is_reserved_symb sym) || (sym = "!=")
                  then
                    give_up ("The prefix symbol " ^ (sym ^ "is reserved..."));
                  sym))
    let mutable_flag = Decap.declare_grammar "mutable_flag"
    let _ =
      Decap.set_grammar mutable_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Mutable) mutable_kw;
           Decap.apply (fun _  -> Immutable) (Decap.empty ())])
    let private_flag = Decap.declare_grammar "private_flag"
    let _ =
      Decap.set_grammar private_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Private) private_kw;
           Decap.apply (fun _  -> Public) (Decap.empty ())])
    let virtual_flag = Decap.declare_grammar "virtual_flag"
    let _ =
      Decap.set_grammar virtual_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Virtual) virtual_kw;
           Decap.apply (fun _  -> Concrete) (Decap.empty ())])
    let rec_flag = Decap.declare_grammar "rec_flag"
    let _ =
      Decap.set_grammar rec_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Recursive) rec_kw;
           Decap.apply (fun _  -> Nonrecursive) (Decap.empty ())])
    let downto_flag = Decap.declare_grammar "downto_flag"
    let _ =
      Decap.set_grammar downto_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Upto) to_kw;
           Decap.apply (fun _default_0  -> Downto) downto_kw])
    let entry_points: (string* entry_point) list ref =
      ref
        [(".mli", (Interface (signature, ocaml_blank)));
        (".ml", (Implementation (structure, ocaml_blank)))]
  end
module type Extension  = module type of Initial
module type FExt  = functor (E : Extension) -> Extension
include Initial
