open Input
open Decap
open Charset
open Asttypes
open Parsetree
open Longident
open Pa_ast
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
    exception Unclosed_comment of int* int
    let blank str pos =
      let rec fn lvl state prev ((str,pos) as cur) =
        let (c,str',pos') = read str pos in
        let next = (str', pos') in
        match (state, c) with
        | (_,'\255') when lvl > 0 ->
            raise (Unclosed_comment ((line_num str), pos))
        | (`Esc,_) -> fn lvl `Str cur next
        | (`Str,'"') -> fn lvl `Ini cur next
        | (`Chr,_) -> fn lvl `Ini cur next
        | (`Str,'\\') -> fn lvl `Esc cur next
        | (`Str,_) -> fn lvl `Str cur next
        | (`StrO l,'a'..'z') -> fn lvl (`StrO (c :: l)) cur next
        | (`StrO l,'|') -> fn lvl (`StrI (List.rev l)) cur next
        | (`StrO _,_) -> fn lvl `Ini cur next
        | (`StrI l,'|') -> fn lvl (`StrC (l, l)) cur next
        | (`StrC (l',a::l),a') when a = a' -> fn lvl (`StrC (l', l)) cur next
        | (`StrC (_,[]),'}') -> fn lvl `Ini cur next
        | (`StrC (l',_),_) -> fn lvl (`StrI l') cur next
        | (_,'"') when lvl > 0 -> fn lvl `Str cur next
        | (_,'\'') when lvl > 0 -> fn lvl `Chr cur next
        | (_,'{') when lvl > 0 -> fn lvl (`StrO []) cur next
        | (`Ini,'(') -> fn lvl `Opn cur next
        | (`Opn,'*') -> fn (lvl + 1) `Ini cur next
        | (`Opn,_) when lvl = 0 -> prev
        | (`Opn,_) -> fn lvl `Ini cur next
        | (`Ini,'*') when lvl = 0 -> cur
        | (`Ini,'*') -> fn lvl `Cls cur next
        | (`Cls,'*') -> fn lvl `Cls cur next
        | (`Cls,')') -> fn (lvl - 1) `Ini cur next
        | (`Cls,_) -> fn lvl `Ini cur next
        | (_,(' '|'\t'|'\r'|'\n')) -> fn lvl `Ini cur next
        | (_,_) when lvl > 0 -> fn lvl `Ini cur next
        | (_,_) -> cur in
      fn 0 `Ini (str, pos) (str, pos)
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
             | `Type of string ] grammar),set_parameter)
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
    let constructor_declaration _loc name args res =
      {
        pcd_name = name;
        pcd_args = args;
        pcd_res = res;
        pcd_attributes = [];
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
    let type_declaration _loc name params cstrs kind priv manifest =
      let params = params_map _loc params in
      {
        ptype_name = name;
        ptype_params = params;
        ptype_cstrs = cstrs;
        ptype_kind = kind;
        ptype_private = priv;
        ptype_manifest = manifest;
        ptype_attributes = [];
        ptype_loc = _loc
      }
    let class_type_declaration _loc' _loc name params virt expr =
      let params = params_map _loc' params in
      {
        pci_params = params;
        pci_virt = virt;
        pci_name = name;
        pci_expr = expr;
        pci_attributes = [];
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
    let module_declaration _loc name mt =
      { pmd_name = name; pmd_type = mt; pmd_attributes = []; pmd_loc = _loc }
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
      try parse_string g blank e'
      with | e -> (Printf.eprintf "Error in quotation: %s\n%!" e'; raise e)
    let par_re s = "\\(" ^ (s ^ "\\)")
    let union_re l =
      let l = List.map (fun s  -> par_re s) l in String.concat "\\|" l
    let lident_re =
      "\\(\\([a-z][a-zA-Z0-9_']*\\)\\|\\([_][a-zA-Z0-9_']+\\)\\)"
    let cident_re = "[A-Z][a-zA-Z0-9_']*"
    let ident_re = "[A-Za-z_][a-zA-Z0-9_']*"
    let make_reserved l =
      let reserved =
        ref (List.sort (fun s  -> fun s'  -> - (compare s s')) l) in
      let re_from_list l =
        Str.regexp
          (String.concat "\\|"
             (List.map (fun s  -> "\\(" ^ ((Str.quote s) ^ "\\)")) l)) in
      let re = ref (re_from_list (!reserved)) in
      ((fun s  ->
          (Str.string_match (!re) s 0) &&
            ((Str.match_end ()) = (String.length s))),
        (fun s  ->
           reserved :=
             (List.sort (fun s  -> fun s'  -> - (compare s s')) (s ::
                (!reserved)));
           re := (re_from_list (!reserved))))
    let (is_reserved_id,add_reserved_id) =
      make_reserved
        ["and";
        "as";
        "assert";
        "asr";
        "begin";
        "class";
        "constraint";
        "do";
        "done";
        "downto";
        "else";
        "end";
        "exception";
        "external";
        "false";
        "for";
        "function";
        "functor";
        "fun";
        "if";
        "in";
        "include";
        "inherit";
        "initializer";
        "land";
        "lazy";
        "let";
        "lor";
        "lsl";
        "lsr";
        "lxor";
        "match";
        "method";
        "mod";
        "module";
        "mutable";
        "new";
        "object";
        "of";
        "open";
        "or";
        "private";
        "rec";
        "sig";
        "struct";
        "then";
        "to";
        "true";
        "try";
        "type";
        "val";
        "virtual";
        "when";
        "while";
        "with"]
    let ident: string grammar =
      regexp ~name:"ident" ident_re
        (fun fn  ->
           let id = fn 0 in
           if is_reserved_id id then give_up (id ^ " is a keyword..."); id)
    let capitalized_ident: string grammar =
      regexp ~name:"capitalized_ident" cident_re (fun fn  -> fn 0)
    let lowercase_ident: string grammar =
      regexp ~name:"lowercase_ident" lident_re
        (fun fn  ->
           let id = fn 0 in
           if is_reserved_id id then give_up (id ^ " is a keyword..."); id)
    let (is_reserved_symb,add_reserved_symb) =
      make_reserved
        ["#";
        "'";
        "(";
        ")";
        ",";
        "->";
        ".";
        "..";
        ":";
        ":>";
        ";";
        ";;";
        "<-";
        ">]";
        ">}";
        "?";
        "[";
        "[<";
        "[>";
        "[|";
        "]";
        "_";
        "`";
        "{";
        "{<";
        "|";
        "|]";
        "}";
        "~"]
    let arrow_re = Decap.declare_grammar "arrow_re"
    let _ =
      Decap.set_grammar arrow_re
        (Decap.regexp ~name:"\\(->\\)\\|\\(\226\134\146\\)"
           "\\(->\\)\\|\\(\226\134\146\\)" (fun groupe  -> groupe 0))
    let not_special =
      not_in_charset
        (List.fold_left add Charset.empty_charset
           ['!';
           '$';
           '%';
           '&';
           '*';
           '+';
           '.';
           '/';
           ':';
           '<';
           '=';
           '>';
           '?';
           '@';
           '^';
           '|';
           '~';
           '-'])
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
    let key_word s =
      let len_s = String.length s in
      assert (len_s > 0);
      black_box
        (fun str  ->
           fun pos  ->
             let str' = ref str in
             let pos' = ref pos in
             for i = 0 to len_s - 1 do
               (let (c,_str',_pos') = read (!str') (!pos') in
                if c <> (s.[i])
                then give_up ("The keyword " ^ (s ^ " was expected..."));
                str' := _str';
                pos' := _pos')
             done;
             (let str' = !str'
              and pos' = !pos' in
              let (c,_,_) = read str' pos' in
              match c with
              | 'a'..'z'|'A'..'Z'|'0'..'9'|'_'|'\'' ->
                  give_up ("The keyword " ^ (s ^ " was expected..."))
              | _ -> ((), str', pos'))) (Charset.singleton (s.[0])) false s
    let mutable_kw = key_word "mutable"
    let mutable_flag = Decap.declare_grammar "mutable_flag"
    let _ =
      Decap.set_grammar mutable_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Mutable) mutable_kw;
           Decap.apply (fun _  -> Immutable) (Decap.empty ())])
    let private_kw = key_word "private"
    let private_flag = Decap.declare_grammar "private_flag"
    let _ =
      Decap.set_grammar private_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Private) private_kw;
           Decap.apply (fun _  -> Public) (Decap.empty ())])
    let virtual_kw = key_word "virtual"
    let virtual_flag = Decap.declare_grammar "virtual_flag"
    let _ =
      Decap.set_grammar virtual_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Virtual) virtual_kw;
           Decap.apply (fun _  -> Concrete) (Decap.empty ())])
    let rec_kw = key_word "rec"
    let rec_flag = Decap.declare_grammar "rec_flag"
    let _ =
      Decap.set_grammar rec_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Recursive) rec_kw;
           Decap.apply (fun _  -> Nonrecursive) (Decap.empty ())])
    let to_kw = key_word "to"
    let downto_kw = key_word "downto"
    let downto_flag = Decap.declare_grammar "downto_flag"
    let _ =
      Decap.set_grammar downto_flag
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> Upto) to_kw;
           Decap.apply (fun _default_0  -> Downto) downto_kw])
    let joker_kw = key_word "_"
    let method_kw = key_word "method"
    let object_kw = key_word "object"
    let class_kw = key_word "class"
    let inherit_kw = key_word "inherit"
    let as_kw = key_word "as"
    let of_kw = key_word "of"
    let module_kw = key_word "module"
    let open_kw = key_word "open"
    let include_kw = key_word "include"
    let type_kw = key_word "type"
    let val_kw = key_word "val"
    let external_kw = key_word "external"
    let constraint_kw = key_word "constraint"
    let begin_kw = key_word "begin"
    let end_kw = key_word "end"
    let and_kw = key_word "and"
    let true_kw = key_word "true"
    let false_kw = key_word "false"
    let exception_kw = key_word "exception"
    let when_kw = key_word "when"
    let fun_kw = key_word "fun"
    let function_kw = key_word "function"
    let let_kw = key_word "let"
    let in_kw = key_word "in"
    let initializer_kw = key_word "initializer"
    let with_kw = key_word "with"
    let while_kw = key_word "while"
    let for_kw = key_word "for"
    let do_kw = key_word "do"
    let done_kw = key_word "done"
    let new_kw = key_word "new"
    let assert_kw = key_word "assert"
    let if_kw = key_word "if"
    let then_kw = key_word "then"
    let else_kw = key_word "else"
    let try_kw = key_word "try"
    let match_kw = key_word "match"
    let struct_kw = key_word "struct"
    let functor_kw = key_word "functor"
    let sig_kw = key_word "sig"
    let lazy_kw = key_word "lazy"
    let parser_kw = key_word "parser"
    let cached_kw = key_word "cached"
    let int_dec_re = "[0-9][0-9_]*[lLn]?"
    let int_hex_re = "[0][xX][0-9a-fA-F][0-9a-fA-F_]*[lLn]?"
    let int_oct_re = "[0][oO][0-7][0-7_]*[lLn]?"
    let int_bin_re = "[0][bB][01][01_]*[lLn]?"
    let int_pos_re =
      union_re [int_hex_re; int_oct_re; int_bin_re; int_dec_re]
    let integer_litteral = Decap.declare_grammar "integer_litteral"
    let _ =
      Decap.set_grammar integer_litteral
        (Decap.apply
           (fun i  ->
              let len = String.length i in
              assert (len > 0);
              (match i.[len - 1] with
               | 'l' ->
                   const_int32 (Int32.of_string (String.sub i 0 (len - 1)))
               | 'L' ->
                   const_int64 (Int64.of_string (String.sub i 0 (len - 1)))
               | 'n' ->
                   const_nativeint
                     (Nativeint.of_string (String.sub i 0 (len - 1)))
               | _ -> const_int (int_of_string i)))
           (Decap.regexp ~name:"int_pos" int_pos_re (fun groupe  -> groupe 0)))
    let bool_lit = Decap.declare_grammar "bool_lit"
    let _ =
      Decap.set_grammar bool_lit
        (Decap.alternatives
           [Decap.apply (fun _default_0  -> "false") false_kw;
           Decap.apply (fun _default_0  -> "true") true_kw])
    let entry_points: (string* entry_point) list ref =
      ref
        [(".mli", (Interface (signature, blank)));
        (".ml", (Implementation (structure, blank)))]
  end
module type Extension  = module type of Initial
module type FExt  = functor (E : Extension) -> Extension
include Initial
