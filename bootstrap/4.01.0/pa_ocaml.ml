open Input
open Decap
open Charset
open Asttypes
open Parsetree
open Longident
open Pa_ast
open Pa_lexing
include Pa_ocaml_prelude
module Make(Initial:Extension) =
  struct
    include Initial
    let ouident = uident
    let uident = Decap.declare_grammar "uident"
    let _ =
      Decap.set_grammar uident
        (Decap.alternatives
           [ouident;
           Decap.fsequence_position (Decap.string "$uid:" "$uid:")
             (Decap.sequence (Decap.ignore_next_blank expression)
                (Decap.char '$' '$')
                (fun e  _  _  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   Quote.string_antiquotation _loc e))])
    let olident = lident
    let lident = Decap.declare_grammar "lident"
    let _ =
      Decap.set_grammar lident
        (Decap.alternatives
           [olident;
           Decap.fsequence_position (Decap.string "$lid:" "$lid:")
             (Decap.sequence (Decap.ignore_next_blank expression)
                (Decap.char '$' '$')
                (fun e  _  _  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   Quote.string_antiquotation _loc e))])
    let oident = ident
    let ident = Decap.declare_grammar "ident"
    let _ =
      Decap.set_grammar ident
        (Decap.alternatives
           [oident;
           Decap.fsequence_position (Decap.string "$ident:" "$ident:")
             (Decap.sequence (Decap.ignore_next_blank expression)
                (Decap.char '$' '$')
                (fun e  _  _  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   Quote.string_antiquotation _loc e))])
    let mk_unary_opp name _loc_name arg _loc_arg =
      let res =
        match (name, (arg.pexp_desc)) with
        | ("-",Pexp_constant (Const_int n)) ->
            Pexp_constant (Const_int (- n))
        | ("-",Pexp_constant (Const_int32 n)) ->
            Pexp_constant (Const_int32 (Int32.neg n))
        | ("-",Pexp_constant (Const_int64 n)) ->
            Pexp_constant (Const_int64 (Int64.neg n))
        | ("-",Pexp_constant (Const_nativeint n)) ->
            Pexp_constant (Const_nativeint (Nativeint.neg n))
        | (("-"|"-."),Pexp_constant (Const_float f)) ->
            Pexp_constant (Const_float ("-" ^ f))
        | ("+",Pexp_constant (Const_int _))
          |("+",Pexp_constant (Const_int32 _))
          |("+",Pexp_constant (Const_int64 _))
          |("+",Pexp_constant (Const_nativeint _))
          |(("+"|"+."),Pexp_constant (Const_float _)) -> arg.pexp_desc
        | (("-"|"-."|"+"|"+."),_) ->
            let p =
              loc_expr _loc_name
                (Pexp_ident (id_loc (Lident ("~" ^ name)) _loc_name)) in
            Pexp_apply (p, [("", arg)])
        | _ ->
            let p =
              loc_expr _loc_name
                (Pexp_ident (id_loc (Lident name) _loc_name)) in
            Pexp_apply (p, [("", arg)]) in
      loc_expr (merge2 _loc_name _loc_arg) res
    let check_variable vl loc v =
      if List.mem v vl
      then raise (let open Syntaxerr in Error (Variable_in_scope (loc, v)))
    let varify_constructors var_names t =
      let rec loop t =
        let desc =
          match t.ptyp_desc with
          | Ptyp_any  -> Ptyp_any
          | Ptyp_var x -> (check_variable var_names t.ptyp_loc x; Ptyp_var x)
          | Ptyp_arrow (label,core_type,core_type') ->
              Ptyp_arrow (label, (loop core_type), (loop core_type'))
          | Ptyp_tuple lst -> Ptyp_tuple (List.map loop lst)
          | Ptyp_constr ({ txt = Lident s },[]) when List.mem s var_names ->
              Ptyp_var s
          | Ptyp_constr (longident,lst) ->
              Ptyp_constr (longident, (List.map loop lst))
          | Ptyp_object lst -> Ptyp_object (List.map loop_core_field lst)
          | Ptyp_class (longident,lst,lbl_list) ->
              Ptyp_class (longident, (List.map loop lst), lbl_list)
          | Ptyp_alias (core_type,string) ->
              (check_variable var_names t.ptyp_loc string;
               Ptyp_alias ((loop core_type), string))
          | Ptyp_variant (row_field_list,flag,lbl_lst_option) ->
              Ptyp_variant
                ((List.map loop_row_field row_field_list), flag,
                  lbl_lst_option)
          | Ptyp_poly (string_lst,core_type) ->
              (List.iter (check_variable var_names t.ptyp_loc) string_lst;
               Ptyp_poly (string_lst, (loop core_type)))
          | Ptyp_package (longident,lst) ->
              Ptyp_package
                (longident, (List.map (fun (n,typ)  -> (n, (loop typ))) lst)) in
        { t with ptyp_desc = desc }
      and loop_core_field t =
        let desc =
          match t.pfield_desc with
          | Pfield (n,typ) -> Pfield (n, (loop typ))
          | Pfield_var  -> Pfield_var in
        { t with pfield_desc = desc }
      and loop_row_field =
        function
        | Rtag (label,flag,lst) -> Rtag (label, flag, (List.map loop lst))
        | Rinherit t -> Rinherit (loop t) in
      loop t
    let wrap_type_annotation _loc newtypes core_type body =
      let exp = loc_expr _loc (pexp_constraint (body, core_type)) in
      let exp =
        List.fold_right
          (fun newtype  exp  -> loc_expr _loc (Pexp_newtype (newtype, exp)))
          newtypes exp in
      (exp,
        (loc_typ _loc
           (Ptyp_poly (newtypes, (varify_constructors newtypes core_type)))))
    let float_litteral = Decap.apply fst Pa_lexing.float_litteral
    let _ = set_grammar char_litteral Pa_lexing.char_litteral
    let _ =
      set_grammar string_litteral (Decap.apply fst Pa_lexing.string_litteral)
    let _ = set_grammar regexp_litteral Pa_lexing.regexp_litteral
    type tree =  
      | Node of tree* tree
      | Leaf of string 
    let string_of_tree (t : tree) =
      (let b = Buffer.create 101 in
       let rec fn =
         function
         | Leaf s -> Buffer.add_string b s
         | Node (a,b) -> (fn a; fn b) in
       fn t; Buffer.contents b : string )
    let label_name = lident
    let label = Decap.declare_grammar "label"
    let _ =
      Decap.set_grammar label
        (Decap.fsequence (Decap.ignore_next_blank (Decap.char '~' '~'))
           (Decap.sequence (Decap.ignore_next_blank label_name) no_colon
              (fun ln  _default_0  _  -> ln)))
    let opt_label = Decap.declare_grammar "opt_label"
    let _ =
      Decap.set_grammar opt_label
        (Decap.fsequence (Decap.ignore_next_blank (Decap.char '?' '?'))
           (Decap.sequence (Decap.ignore_next_blank label_name) no_colon
              (fun ln  _default_0  _  -> ln)))
    let ty_label = Decap.declare_grammar "ty_label"
    let _ =
      Decap.set_grammar ty_label
        (Decap.fsequence (Decap.ignore_next_blank (Decap.char '~' '~'))
           (Decap.sequence (Decap.ignore_next_blank lident)
              (Decap.char ':' ':') (fun s  _  _  -> labelled s)))
    let ty_opt_label = Decap.declare_grammar "ty_opt_label"
    let _ =
      Decap.set_grammar ty_opt_label
        (Decap.fsequence (Decap.ignore_next_blank (Decap.char '?' '?'))
           (Decap.sequence (Decap.ignore_next_blank lident)
              (Decap.char ':' ':') (fun s  _  _  -> optional s)))
    let maybe_opt_label = Decap.declare_grammar "maybe_opt_label"
    let _ =
      Decap.set_grammar maybe_opt_label
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x) (Decap.string "?" "?")))
           label_name
           (fun o  ln  -> if o = None then labelled ln else optional ln))
    let operator_name = Decap.declare_grammar "operator_name"
    let _ =
      Decap.set_grammar operator_name
        (Decap.alternatives
           [alternatives (List.map infix_symbol infix_prios);
           alternatives (List.map prefix_symbol prefix_prios)])
    let value_name = Decap.declare_grammar "value_name"
    let _ =
      Decap.set_grammar value_name
        (Decap.alternatives
           [lident;
           Decap.fsequence (Decap.char '(' '(')
             (Decap.sequence operator_name (Decap.char ')' ')')
                (fun op  _  _  -> op))])
    let constr_name = uident
    let tag_name = Decap.declare_grammar "tag_name"
    let _ =
      Decap.set_grammar tag_name
        (Decap.sequence (Decap.string "`" "`") ident (fun _  c  -> c))
    let typeconstr_name = lident
    let field_name = lident
    let smodule_name = uident
    let module_name = Decap.declare_grammar "module_name"
    let _ =
      Decap.set_grammar module_name
        (Decap.apply_position
           (fun u  __loc__start__buf  __loc__start__pos  __loc__end__buf 
              __loc__end__pos  ->
              let _loc =
                locate __loc__start__buf __loc__start__pos __loc__end__buf
                  __loc__end__pos in
              id_loc u _loc) uident)
    let modtype_name = ident
    let class_name = lident
    let inst_var_name = lident
    let method_name = lident
    let (module_path_gen,set_module_path_gen) =
      grammar_family "module_path_gen"
    let (module_path_suit,set_module_path_suit) =
      grammar_family "module_path_suit"
    let (module_path_suit_aux,module_path_suit_aux__set__grammar) =
      Decap.grammar_family "module_path_suit_aux"
    let _ =
      module_path_suit_aux__set__grammar
        (fun allow_app  ->
           Decap.alternatives
             (let y =
                [Decap.sequence (Decap.string "." ".") smodule_name
                   (fun _  m  acc  -> Ldot (acc, m))] in
              if allow_app
              then
                (Decap.fsequence (Decap.string "(" "(")
                   (Decap.sequence (module_path_gen true)
                      (Decap.string ")" ")")
                      (fun m'  _  _  a  -> Lapply (a, m'))))
                :: y
              else y))
    let _ =
      set_module_path_suit
        (fun allow_app  ->
           Decap.alternatives
             [Decap.sequence (module_path_suit_aux allow_app)
                (module_path_suit allow_app) (fun f  g  acc  -> g (f acc));
             Decap.apply (fun _  acc  -> acc) (Decap.empty ())])
    let _ =
      set_module_path_gen
        (fun allow_app  ->
           Decap.sequence smodule_name (module_path_suit allow_app)
             (fun m  s  -> s (Lident m)))
    let module_path = module_path_gen false
    let extended_module_path = module_path_gen true
    let _ =
      set_grammar value_path
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence module_path (Decap.string "." ".")
                    (fun m  _  -> m)))) value_name
           (fun mp  vn  ->
              match mp with | None  -> Lident vn | Some p -> Ldot (p, vn)))
    let constr = Decap.declare_grammar "constr"
    let _ =
      Decap.set_grammar constr
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence module_path (Decap.string "." ".")
                    (fun m  _  -> m)))) constr_name
           (fun mp  cn  ->
              match mp with | None  -> Lident cn | Some p -> Ldot (p, cn)))
    let typeconstr = Decap.declare_grammar "typeconstr"
    let _ =
      Decap.set_grammar typeconstr
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence extended_module_path (Decap.string "." ".")
                    (fun m  _  -> m)))) typeconstr_name
           (fun mp  tcn  ->
              match mp with | None  -> Lident tcn | Some p -> Ldot (p, tcn)))
    let field = Decap.declare_grammar "field"
    let _ =
      Decap.set_grammar field
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence module_path (Decap.string "." ".")
                    (fun m  _  -> m)))) field_name
           (fun mp  fn  ->
              match mp with | None  -> Lident fn | Some p -> Ldot (p, fn)))
    let class_path = Decap.declare_grammar "class_path"
    let _ =
      Decap.set_grammar class_path
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence module_path (Decap.string "." ".")
                    (fun m  _  -> m)))) class_name
           (fun mp  cn  ->
              match mp with | None  -> Lident cn | Some p -> Ldot (p, cn)))
    let modtype_path = Decap.declare_grammar "modtype_path"
    let _ =
      Decap.set_grammar modtype_path
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence extended_module_path (Decap.string "." ".")
                    (fun m  _  -> m)))) modtype_name
           (fun mp  mtn  ->
              match mp with | None  -> Lident mtn | Some p -> Ldot (p, mtn)))
    let classtype_path = Decap.declare_grammar "classtype_path"
    let _ =
      Decap.set_grammar classtype_path
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence extended_module_path (Decap.string "." ".")
                    (fun m  _  -> m)))) class_name
           (fun mp  cn  ->
              match mp with | None  -> Lident cn | Some p -> Ldot (p, cn)))
    let opt_variance = Decap.declare_grammar "opt_variance"
    let _ =
      Decap.set_grammar opt_variance
        (Decap.apply
           (fun v  ->
              match v with
              | None  -> (false, false)
              | Some "+" -> (true, false)
              | Some "-" -> (false, true)
              | _ -> assert false)
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.regexp "[+-]" (fun groupe  -> groupe 0)))))
    let override_flag = Decap.declare_grammar "override_flag"
    let _ =
      Decap.set_grammar override_flag
        (Decap.apply (fun o  -> if o <> None then Override else Fresh)
           (Decap.option None
              (Decap.apply (fun x  -> Some x) (Decap.string "!" "!"))))
    let attr_id = Decap.declare_grammar "attr_id"
    let _ =
      Decap.set_grammar attr_id
        (Decap.sequence_position ident
           (Decap.apply List.rev
              (Decap.fixpoint []
                 (Decap.apply (fun x  y  -> x :: y)
                    (Decap.sequence (Decap.char '.' '.') ident
                       (fun _  id  -> id)))))
           (fun id  l  __loc__start__buf  __loc__start__pos  __loc__end__buf 
              __loc__end__pos  ->
              let _loc =
                locate __loc__start__buf __loc__start__pos __loc__end__buf
                  __loc__end__pos in
              id_loc (String.concat "." (id :: l)) _loc))
    type attr =  
      | PStr of structure_item list
      | PTyp of core_type
      | PPat of pattern* expression option 
    let payload = Decap.declare_grammar "payload"
    let _ =
      Decap.set_grammar payload
        (Decap.alternatives
           [Decap.apply (fun s  -> PStr s) structure;
           Decap.sequence (Decap.char ':' ':') typexpr (fun _  t  -> PTyp t);
           Decap.fsequence (Decap.char '?' '?')
             (Decap.sequence pattern
                (Decap.option None
                   (Decap.apply (fun x  -> Some x)
                      (Decap.sequence (Decap.string "when" "when") expression
                         (fun _  e  -> e)))) (fun p  e  _  -> PPat (p, e)))])
    let attribute = Decap.declare_grammar "attribute"
    let _ =
      Decap.set_grammar attribute
        (Decap.fsequence (Decap.string "[@" "[@")
           (Decap.sequence attr_id payload (fun id  p  _  -> (id, p))))
    let attributes = Decap.declare_grammar "attributes"
    let _ =
      Decap.set_grammar attributes
        (Decap.apply List.rev
           (Decap.fixpoint [] (Decap.apply (fun x  y  -> x :: y) attribute)))
    let ext_attributes = Decap.declare_grammar "ext_attributes"
    let _ =
      Decap.set_grammar ext_attributes
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence (Decap.char '%' '%') attribute
                    (fun _  a  -> a)))) attributes (fun a  l  -> (a, l)))
    let post_item_attributes = Decap.declare_grammar "post_item_attributes"
    let _ =
      Decap.set_grammar post_item_attributes
        (Decap.apply List.rev
           (Decap.fixpoint []
              (Decap.apply (fun x  y  -> x :: y)
                 (Decap.fsequence (Decap.string "[@@" "[@@")
                    (Decap.fsequence attr_id
                       (Decap.sequence payload (Decap.char ']' ']')
                          (fun p  _  id  _  -> (id, p))))))))
    let ext_attributes = Decap.declare_grammar "ext_attributes"
    let _ =
      Decap.set_grammar ext_attributes
        (Decap.apply List.rev
           (Decap.fixpoint []
              (Decap.apply (fun x  y  -> x :: y)
                 (Decap.fsequence (Decap.string "[@@@" "[@@@")
                    (Decap.fsequence attr_id
                       (Decap.sequence payload (Decap.char ']' ']')
                          (fun p  _  id  _  -> (id, p))))))))
    let extension = Decap.declare_grammar "extension"
    let _ =
      Decap.set_grammar extension
        (Decap.fsequence (Decap.string "[%" "[%")
           (Decap.fsequence attr_id
              (Decap.sequence payload (Decap.char ']' ']')
                 (fun p  _  id  _  -> (id, p)))))
    let item_extension = Decap.declare_grammar "item_extension"
    let _ =
      Decap.set_grammar item_extension
        (Decap.fsequence (Decap.string "[%%" "[%%")
           (Decap.fsequence attr_id
              (Decap.sequence payload (Decap.char ']' ']')
                 (fun p  _  id  _  -> (id, p)))))
    let only_poly_typexpr = Decap.declare_grammar "only_poly_typexpr"
    let _ =
      Decap.set_grammar only_poly_typexpr
        (Decap.fsequence_position
           (Decap.apply List.rev
              (Decap.fixpoint1 []
                 (Decap.apply (fun x  y  -> x :: y)
                    (Decap.sequence (Decap.string "'" "'") ident
                       (fun _  id  -> id)))))
           (Decap.sequence (Decap.string "." ".") typexpr
              (fun _  te  ids  __loc__start__buf  __loc__start__pos 
                 __loc__end__buf  __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 loc_typ _loc (Ptyp_poly (ids, te)))))
    let poly_typexpr = Decap.declare_grammar "poly_typexpr"
    let _ =
      Decap.set_grammar poly_typexpr
        (Decap.alternatives
           [Decap.fsequence_position
              (Decap.apply List.rev
                 (Decap.fixpoint1 []
                    (Decap.apply (fun x  y  -> x :: y)
                       (Decap.sequence (Decap.string "'" "'") ident
                          (fun _  id  -> id)))))
              (Decap.sequence (Decap.string "." ".") typexpr
                 (fun _  te  ids  __loc__start__buf  __loc__start__pos 
                    __loc__end__buf  __loc__end__pos  ->
                    let _loc =
                      locate __loc__start__buf __loc__start__pos
                        __loc__end__buf __loc__end__pos in
                    loc_typ _loc (Ptyp_poly (ids, te))));
           Decap.apply_position
             (fun te  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_typ _loc (Ptyp_poly ([], te))) typexpr])
    let poly_syntax_typexpr = Decap.declare_grammar "poly_syntax_typexpr"
    let _ =
      Decap.set_grammar poly_syntax_typexpr
        (Decap.fsequence type_kw
           (Decap.fsequence
              (Decap.apply List.rev
                 (Decap.fixpoint1 []
                    (Decap.apply (fun x  y  -> x :: y) typeconstr_name)))
              (Decap.sequence (Decap.string "." ".") typexpr
                 (fun _  te  ids  _default_0  -> (ids, te)))))
    let method_type = Decap.declare_grammar "method_type"
    let _ =
      Decap.set_grammar method_type
        (Decap.fsequence_position method_name
           (Decap.sequence (Decap.string ":" ":") poly_typexpr
              (fun _  pte  mn  __loc__start__buf  __loc__start__pos 
                 __loc__end__buf  __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 { pfield_desc = (Pfield (mn, pte)); pfield_loc = _loc })))
    let tag_spec = Decap.declare_grammar "tag_spec"
    let _ =
      Decap.set_grammar tag_spec
        (Decap.alternatives
           [Decap.sequence tag_name
              (Decap.option None
                 (Decap.apply (fun x  -> Some x)
                    (Decap.fsequence of_kw
                       (Decap.sequence
                          (Decap.option None
                             (Decap.apply (fun x  -> Some x)
                                (Decap.char '&' '&'))) typexpr
                          (fun _default_1  _default_0  _  ->
                             (_default_1, _default_0))))))
              (fun tn  te  ->
                 let (amp,t) =
                   match te with
                   | None  -> (true, [])
                   | Some (amp,l) -> ((amp <> None), [l]) in
                 Rtag (tn, amp, t));
           Decap.apply (fun te  -> Rinherit te) typexpr])
    let tag_spec_first = Decap.declare_grammar "tag_spec_first"
    let _ =
      Decap.set_grammar tag_spec_first
        (Decap.alternatives
           [Decap.sequence tag_name
              (Decap.option None
                 (Decap.apply (fun x  -> Some x)
                    (Decap.fsequence of_kw
                       (Decap.sequence
                          (Decap.option None
                             (Decap.apply (fun x  -> Some x)
                                (Decap.char '&' '&'))) typexpr
                          (fun _default_1  _default_0  _  ->
                             (_default_1, _default_0))))))
              (fun tn  te  ->
                 let (amp,t) =
                   match te with
                   | None  -> (true, [])
                   | Some (amp,l) -> ((amp <> None), [l]) in
                 [Rtag (tn, amp, t)]);
           Decap.fsequence
             (Decap.option None (Decap.apply (fun x  -> Some x) typexpr))
             (Decap.sequence (Decap.string "|" "|") tag_spec
                (fun _  ts  te  ->
                   match te with
                   | None  -> [ts]
                   | Some te -> [Rinherit te; ts]))])
    let tag_spec_full = Decap.declare_grammar "tag_spec_full"
    let _ =
      Decap.set_grammar tag_spec_full
        (Decap.alternatives
           [Decap.sequence tag_name
              (Decap.option (true, [])
                 (Decap.fsequence of_kw
                    (Decap.fsequence
                       (Decap.option None
                          (Decap.apply (fun x  -> Some x)
                             (Decap.char '&' '&')))
                       (Decap.sequence typexpr
                          (Decap.apply List.rev
                             (Decap.fixpoint []
                                (Decap.apply (fun x  y  -> x :: y)
                                   (Decap.sequence (Decap.string "&" "&")
                                      typexpr (fun _  te  -> te)))))
                          (fun te  tes  amp  _default_0  ->
                             ((amp <> None), (te :: tes)))))))
              (fun tn  ((amp,tes) as _default_0)  -> Rtag (tn, amp, tes));
           Decap.apply (fun te  -> Rinherit te) typexpr])
    let polymorphic_variant_type : core_type grammar=
      Decap.declare_grammar "polymorphic_variant_type"
    let _ =
      Decap.set_grammar polymorphic_variant_type
        (Decap.alternatives
           [Decap.fsequence_position (Decap.string "[" "[")
              (Decap.fsequence tag_spec_first
                 (Decap.sequence
                    (Decap.apply List.rev
                       (Decap.fixpoint []
                          (Decap.apply (fun x  y  -> x :: y)
                             (Decap.sequence (Decap.string "|" "|") tag_spec
                                (fun _  ts  -> ts))))) (Decap.string "]" "]")
                    (fun tss  _  tsf  _  __loc__start__buf  __loc__start__pos
                        __loc__end__buf  __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos in
                       let flag = true in
                       loc_typ _loc (Ptyp_variant ((tsf @ tss), flag, None)))));
           Decap.fsequence_position (Decap.string "[>" "[>")
             (Decap.fsequence
                (Decap.option None (Decap.apply (fun x  -> Some x) tag_spec))
                (Decap.sequence
                   (Decap.apply List.rev
                      (Decap.fixpoint []
                         (Decap.apply (fun x  y  -> x :: y)
                            (Decap.sequence (Decap.string "|" "|") tag_spec
                               (fun _  ts  -> ts))))) (Decap.string "]" "]")
                   (fun tss  _  ts  _  __loc__start__buf  __loc__start__pos 
                      __loc__end__buf  __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      let tss =
                        match ts with | None  -> tss | Some ts -> ts :: tss in
                      let flag = false in
                      loc_typ _loc (Ptyp_variant (tss, flag, None)))));
           Decap.fsequence_position (Decap.string "[<" "[<")
             (Decap.fsequence
                (Decap.option None
                   (Decap.apply (fun x  -> Some x) (Decap.string "|" "|")))
                (Decap.fsequence tag_spec_full
                   (Decap.fsequence
                      (Decap.apply List.rev
                         (Decap.fixpoint []
                            (Decap.apply (fun x  y  -> x :: y)
                               (Decap.sequence (Decap.string "|" "|")
                                  tag_spec_full (fun _  tsf  -> tsf)))))
                      (Decap.sequence
                         (Decap.option []
                            (Decap.sequence (Decap.string ">" ">")
                               (Decap.apply List.rev
                                  (Decap.fixpoint1 []
                                     (Decap.apply (fun x  y  -> x :: y)
                                        tag_name))) (fun _  tns  -> tns)))
                         (Decap.string "]" "]")
                         (fun tns  _  tfss  tfs  _default_0  _ 
                            __loc__start__buf  __loc__start__pos 
                            __loc__end__buf  __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            let flag = true in
                            loc_typ _loc
                              (Ptyp_variant ((tfs :: tfss), flag, (Some tns))))))))])
    let package_constraint = Decap.declare_grammar "package_constraint"
    let _ =
      Decap.set_grammar package_constraint
        (Decap.fsequence type_kw
           (Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) typeconstr)
              (Decap.sequence (Decap.char '=' '=') typexpr
                 (fun _  te  tc  ->
                    let (_loc_tc,tc) = tc in
                    fun _default_0  -> let tc = id_loc tc _loc_tc in (tc, te)))))
    let package_type = Decap.declare_grammar "package_type"
    let _ =
      Decap.set_grammar package_type
        (Decap.sequence
           (Decap.apply_position
              (fun x  str  pos  str'  pos'  ->
                 ((locate str pos str' pos'), x)) modtype_path)
           (Decap.option []
              (Decap.fsequence with_kw
                 (Decap.sequence package_constraint
                    (Decap.apply List.rev
                       (Decap.fixpoint []
                          (Decap.apply (fun x  y  -> x :: y)
                             (Decap.sequence and_kw package_constraint
                                (fun _  _default_0  -> _default_0)))))
                    (fun pc  pcs  _default_0  -> pc :: pcs))))
           (fun mtp  ->
              let (_loc_mtp,mtp) = mtp in
              fun cs  ->
                let mtp = id_loc mtp _loc_mtp in Ptyp_package (mtp, cs)))
    let opt_present = Decap.declare_grammar "opt_present"
    let _ =
      Decap.set_grammar opt_present
        (Decap.alternatives
           [Decap.fsequence (Decap.string "[>" "[>")
              (Decap.sequence
                 (Decap.apply List.rev
                    (Decap.fixpoint1 []
                       (Decap.apply (fun x  y  -> x :: y) tag_name)))
                 (Decap.string "]" "]") (fun l  _  _  -> l));
           Decap.apply (fun _  -> []) (Decap.empty ())])
    let mkoption loc d =
      let loc = ghost loc in
      loc_typ loc
        (Ptyp_constr
           ((id_loc (Ldot ((Lident "*predef*"), "option")) loc), [d]))
    let extra_types_grammar lvl =
      alternatives (List.map (fun g  -> g lvl) extra_types)
    let _ =
      set_typexpr_lvl
        (fun lvl  ->
           Decap.alternatives ((extra_types_grammar lvl) ::
             (let y =
                let y =
                  let y =
                    let y =
                      let y =
                        let y =
                          let y =
                            let y =
                              let y =
                                let y =
                                  let y =
                                    let y =
                                      let y =
                                        let y =
                                          let y =
                                            let y =
                                              let y =
                                                let y =
                                                  let y =
                                                    let y = [] in
                                                    if lvl = AtomType
                                                    then
                                                      (Decap.fsequence_position
                                                         (Decap.ignore_next_blank
                                                            (Decap.char '$'
                                                               '$'))
                                                         (Decap.fsequence
                                                            (Decap.option
                                                               "type"
                                                               (Decap.sequence
                                                                  (Decap.ignore_next_blank
                                                                    (Decap.regexp
                                                                    ~name:"[a-z]+"
                                                                    "[a-z]+"
                                                                    (fun
                                                                    groupe 
                                                                    ->
                                                                    groupe 0)))
                                                                  (Decap.char
                                                                    ':' ':')
                                                                  (fun
                                                                    _default_0
                                                                     _  ->
                                                                    _default_0)))
                                                            (Decap.sequence
                                                               (Decap.ignore_next_blank
                                                                  expression)
                                                               (Decap.char
                                                                  '$' '$')
                                                               (fun e  _  aq 
                                                                  _ 
                                                                  __loc__start__buf
                                                                   __loc__start__pos
                                                                   __loc__end__buf
                                                                   __loc__end__pos
                                                                   ->
                                                                  let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                  let open Quote in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let generic_antiquote
                                                                    e =
                                                                    function
                                                                    | 
                                                                    Quote_ptyp
                                                                     -> e
                                                                    | 
                                                                    _ ->
                                                                    failwith
                                                                    "invalid antiquotation type" in
                                                                    let f =
                                                                    match aq
                                                                    with
                                                                    | 
                                                                    "type" ->
                                                                    generic_antiquote
                                                                    e
                                                                    | 
                                                                    "tuple"
                                                                    ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "typ_tuple")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    _ ->
                                                                    give_up
                                                                    "bad antiquotation" in
                                                                    Quote.ptyp_antiquotation
                                                                    _loc f))))
                                                      :: y
                                                    else y in
                                                  if lvl = DashType
                                                  then
                                                    (Decap.fsequence_position
                                                       (typexpr_lvl DashType)
                                                       (Decap.fsequence
                                                          (Decap.string "#"
                                                             "#")
                                                          (Decap.sequence
                                                             (Decap.apply_position
                                                                (fun x  str 
                                                                   pos  str' 
                                                                   pos'  ->
                                                                   ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                class_path)
                                                             opt_present
                                                             (fun cp  ->
                                                                let (_loc_cp,cp)
                                                                  = cp in
                                                                fun o  _  te 
                                                                  __loc__start__buf
                                                                   __loc__start__pos
                                                                   __loc__end__buf
                                                                   __loc__end__pos
                                                                   ->
                                                                  let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                  let cp =
                                                                    id_loc cp
                                                                    _loc_cp in
                                                                  loc_typ
                                                                    _loc
                                                                    (
                                                                    Ptyp_class
                                                                    (cp,
                                                                    [te], o))))))
                                                    :: y
                                                  else y in
                                                if lvl = As
                                                then
                                                  (Decap.fsequence_position
                                                     (typexpr_lvl As)
                                                     (Decap.fsequence as_kw
                                                        (Decap.sequence
                                                           (Decap.string "'"
                                                              "'") ident
                                                           (fun _  id 
                                                              _default_0  te 
                                                              __loc__start__buf
                                                               __loc__start__pos
                                                               __loc__end__buf
                                                               __loc__end__pos
                                                               ->
                                                              let _loc =
                                                                locate
                                                                  __loc__start__buf
                                                                  __loc__start__pos
                                                                  __loc__end__buf
                                                                  __loc__end__pos in
                                                              loc_typ _loc
                                                                (Ptyp_alias
                                                                   (te, id))))))
                                                  :: y
                                                else y in
                                              if lvl = ProdType
                                              then
                                                (Decap.sequence_position
                                                   (typexpr_lvl
                                                      (next_type_prio
                                                         ProdType))
                                                   (Decap.apply List.rev
                                                      (Decap.fixpoint1 []
                                                         (Decap.apply
                                                            (fun x  y  -> x
                                                               :: y)
                                                            (Decap.sequence
                                                               (Decap.string
                                                                  "*" "*")
                                                               (typexpr_lvl
                                                                  (next_type_prio
                                                                    ProdType))
                                                               (fun _  te  ->
                                                                  te)))))
                                                   (fun te  tes 
                                                      __loc__start__buf 
                                                      __loc__start__pos 
                                                      __loc__end__buf 
                                                      __loc__end__pos  ->
                                                      let _loc =
                                                        locate
                                                          __loc__start__buf
                                                          __loc__start__pos
                                                          __loc__end__buf
                                                          __loc__end__pos in
                                                      loc_typ _loc
                                                        (Ptyp_tuple (te ::
                                                           tes))))
                                                :: y
                                              else y in
                                            if lvl = AtomType
                                            then
                                              (Decap.fsequence_position
                                                 (Decap.string "(" "(")
                                                 (Decap.fsequence typexpr
                                                    (Decap.fsequence
                                                       (Decap.apply List.rev
                                                          (Decap.fixpoint []
                                                             (Decap.apply
                                                                (fun x  y  ->
                                                                   x :: y)
                                                                (Decap.sequence
                                                                   (Decap.string
                                                                    "," ",")
                                                                   typexpr
                                                                   (fun _  te
                                                                     -> te)))))
                                                       (Decap.fsequence
                                                          (Decap.string ")"
                                                             ")")
                                                          (Decap.fsequence
                                                             (Decap.string
                                                                "#" "#")
                                                             (Decap.sequence
                                                                (Decap.apply_position
                                                                   (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                   class_path)
                                                                opt_present
                                                                (fun cp  ->
                                                                   let 
                                                                    (_loc_cp,cp)
                                                                    = cp in
                                                                   fun o  _ 
                                                                    _  tes 
                                                                    te  _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let cp =
                                                                    id_loc cp
                                                                    _loc_cp in
                                                                    loc_typ
                                                                    _loc
                                                                    (Ptyp_class
                                                                    (cp, (te
                                                                    :: tes),
                                                                    o)))))))))
                                              :: y
                                            else y in
                                          if lvl = AtomType
                                          then
                                            (Decap.fsequence_position
                                               (Decap.string "#" "#")
                                               (Decap.sequence
                                                  (Decap.apply_position
                                                     (fun x  str  pos  str' 
                                                        pos'  ->
                                                        ((locate str pos str'
                                                            pos'), x))
                                                     class_path) opt_present
                                                  (fun cp  ->
                                                     let (_loc_cp,cp) = cp in
                                                     fun o  _ 
                                                       __loc__start__buf 
                                                       __loc__start__pos 
                                                       __loc__end__buf 
                                                       __loc__end__pos  ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       let cp =
                                                         id_loc cp _loc_cp in
                                                       loc_typ _loc
                                                         (Ptyp_class
                                                            (cp, [], o)))))
                                            :: y
                                          else y in
                                        if lvl = AtomType
                                        then
                                          (Decap.fsequence_position
                                             (Decap.string "<" "<")
                                             (Decap.fsequence method_type
                                                (Decap.fsequence
                                                   (Decap.apply List.rev
                                                      (Decap.fixpoint []
                                                         (Decap.apply
                                                            (fun x  y  -> x
                                                               :: y)
                                                            (Decap.sequence
                                                               semi_col
                                                               method_type
                                                               (fun _  mt  ->
                                                                  mt)))))
                                                   (Decap.sequence
                                                      (Decap.apply_position
                                                         (fun x  str  pos 
                                                            str'  pos'  ->
                                                            ((locate str pos
                                                                str' pos'),
                                                              x))
                                                         (Decap.option None
                                                            (Decap.apply
                                                               (fun x  ->
                                                                  Some x)
                                                               (Decap.sequence
                                                                  semi_col
                                                                  (Decap.option
                                                                    None
                                                                    (Decap.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Decap.string
                                                                    ".." "..")))
                                                                  (fun _  rv 
                                                                    -> rv)))))
                                                      (Decap.char '>' '>')
                                                      (fun rv  ->
                                                         let (_loc_rv,rv) =
                                                           rv in
                                                         fun _  mts  mt  _ 
                                                           __loc__start__buf 
                                                           __loc__start__pos 
                                                           __loc__end__buf 
                                                           __loc__end__pos 
                                                           ->
                                                           let _loc =
                                                             locate
                                                               __loc__start__buf
                                                               __loc__start__pos
                                                               __loc__end__buf
                                                               __loc__end__pos in
                                                           let ml =
                                                             if
                                                               (rv = None) ||
                                                                 (rv =
                                                                    (
                                                                    Some None))
                                                             then []
                                                             else
                                                               [{
                                                                  pfield_desc
                                                                    =
                                                                    Pfield_var;
                                                                  pfield_loc
                                                                    = _loc_rv
                                                                }] in
                                                           loc_typ _loc
                                                             (Ptyp_object
                                                                ((mt :: mts)
                                                                   @ ml)))))))
                                          :: y
                                        else y in
                                      if lvl = AtomType
                                      then
                                        (Decap.fsequence_position
                                           (Decap.char '<' '<')
                                           (Decap.sequence
                                              (Decap.apply_position
                                                 (fun x  str  pos  str'  pos'
                                                     ->
                                                    ((locate str pos str'
                                                        pos'), x))
                                                 (Decap.option None
                                                    (Decap.apply
                                                       (fun x  -> Some x)
                                                       (Decap.string ".."
                                                          ".."))))
                                              (Decap.char '>' '>')
                                              (fun rv  ->
                                                 let (_loc_rv,rv) = rv in
                                                 fun _  _  __loc__start__buf 
                                                   __loc__start__pos 
                                                   __loc__end__buf 
                                                   __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let ml =
                                                     if rv = None
                                                     then []
                                                     else
                                                       [{
                                                          pfield_desc =
                                                            Pfield_var;
                                                          pfield_loc =
                                                            _loc_rv
                                                        }] in
                                                   loc_typ _loc
                                                     (Ptyp_object ml))))
                                        :: y
                                      else y in
                                    if lvl = AtomType
                                    then polymorphic_variant_type :: y
                                    else y in
                                  if lvl = AppType
                                  then
                                    (Decap.sequence_position
                                       (typexpr_lvl AppType)
                                       (Decap.apply_position
                                          (fun x  str  pos  str'  pos'  ->
                                             ((locate str pos str' pos'), x))
                                          typeconstr)
                                       (fun t  tc  ->
                                          let (_loc_tc,tc) = tc in
                                          fun __loc__start__buf 
                                            __loc__start__pos 
                                            __loc__end__buf  __loc__end__pos 
                                            ->
                                            let _loc =
                                              locate __loc__start__buf
                                                __loc__start__pos
                                                __loc__end__buf
                                                __loc__end__pos in
                                            let constr = id_loc tc _loc_tc in
                                            loc_typ _loc
                                              (Ptyp_constr (constr, [t]))))
                                    :: y
                                  else y in
                                if lvl = AppType
                                then
                                  (Decap.fsequence_position
                                     (Decap.char '(' '(')
                                     (Decap.fsequence typexpr
                                        (Decap.fsequence
                                           (Decap.apply List.rev
                                              (Decap.fixpoint1 []
                                                 (Decap.apply
                                                    (fun x  y  -> x :: y)
                                                    (Decap.sequence
                                                       (Decap.char ',' ',')
                                                       typexpr
                                                       (fun _  te  -> te)))))
                                           (Decap.sequence
                                              (Decap.char ')' ')')
                                              (Decap.apply_position
                                                 (fun x  str  pos  str'  pos'
                                                     ->
                                                    ((locate str pos str'
                                                        pos'), x)) typeconstr)
                                              (fun _  tc  ->
                                                 let (_loc_tc,tc) = tc in
                                                 fun tes  te  _ 
                                                   __loc__start__buf 
                                                   __loc__start__pos 
                                                   __loc__end__buf 
                                                   __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let constr =
                                                     id_loc tc _loc_tc in
                                                   loc_typ _loc
                                                     (Ptyp_constr
                                                        (constr, (te :: tes))))))))
                                  :: y
                                else y in
                              if lvl = AtomType
                              then
                                (Decap.apply_position
                                   (fun tc  ->
                                      let (_loc_tc,tc) = tc in
                                      fun __loc__start__buf 
                                        __loc__start__pos  __loc__end__buf 
                                        __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        loc_typ _loc
                                          (Ptyp_constr
                                             ((id_loc tc _loc_tc), [])))
                                   (Decap.apply_position
                                      (fun x  str  pos  str'  pos'  ->
                                         ((locate str pos str' pos'), x))
                                      typeconstr))
                                :: y
                              else y in
                            if lvl = Arr
                            then
                              (Decap.fsequence_position
                                 (typexpr_lvl (next_type_prio Arr))
                                 (Decap.sequence arrow_re (typexpr_lvl Arr)
                                    (fun _default_0  te'  te 
                                       __loc__start__buf  __loc__start__pos 
                                       __loc__end__buf  __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       loc_typ _loc
                                         (Ptyp_arrow (nolabel, te, te')))))
                              :: y
                            else y in
                          if lvl = Arr
                          then
                            (Decap.fsequence_position label_name
                               (Decap.fsequence (Decap.char ':' ':')
                                  (Decap.fsequence
                                     (typexpr_lvl (next_type_prio Arr))
                                     (Decap.sequence arrow_re
                                        (typexpr_lvl Arr)
                                        (fun _default_0  te'  te  _  ln 
                                           __loc__start__buf 
                                           __loc__start__pos  __loc__end__buf
                                            __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           loc_typ _loc
                                             (Ptyp_arrow
                                                ((labelled ln), te, te')))))))
                            :: y
                          else y in
                        if lvl = Arr
                        then
                          (Decap.fsequence_position ty_opt_label
                             (Decap.fsequence
                                (Decap.apply_position
                                   (fun x  str  pos  str'  pos'  ->
                                      ((locate str pos str' pos'), x))
                                   (typexpr_lvl (next_type_prio Arr)))
                                (Decap.sequence arrow_re (typexpr_lvl Arr)
                                   (fun _default_0  te'  te  ->
                                      let (_loc_te,te) = te in
                                      fun ln  __loc__start__buf 
                                        __loc__start__pos  __loc__end__buf 
                                        __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        loc_typ _loc
                                          (Ptyp_arrow
                                             (ln, (mkoption _loc_te te), te'))))))
                          :: y
                        else y in
                      if lvl = AtomType
                      then
                        (Decap.fsequence (Decap.char '(' '(')
                           (Decap.sequence typexpr (Decap.char ')' ')')
                              (fun te  _  _  -> te)))
                        :: y
                      else y in
                    if lvl = AtomType
                    then
                      (Decap.fsequence_position (Decap.char '(' '(')
                         (Decap.fsequence module_kw
                            (Decap.sequence package_type (Decap.char ')' ')')
                               (fun pt  _  _default_0  _  __loc__start__buf 
                                  __loc__start__pos  __loc__end__buf 
                                  __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  loc_typ _loc pt))))
                      :: y
                    else y in
                  if lvl = AtomType
                  then
                    (Decap.apply_position
                       (fun _default_0  __loc__start__buf  __loc__start__pos 
                          __loc__end__buf  __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          loc_typ _loc Ptyp_any) joker_kw)
                    :: y
                  else y in
                if lvl = AtomType
                then
                  (Decap.sequence_position (Decap.string "'" "'") ident
                     (fun _  id  __loc__start__buf  __loc__start__pos 
                        __loc__end__buf  __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_typ _loc (Ptyp_var id)))
                  :: y
                else y in
              if lvl < AtomType
              then (typexpr_lvl (next_type_prio lvl)) :: y
              else y)))
    let type_param = Decap.declare_grammar "type_param"
    let _ =
      Decap.set_grammar type_param
        (Decap.alternatives
           [Decap.fsequence opt_variance
              (Decap.sequence (Decap.char '\'' '\'')
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) ident)
                 (fun _  id  ->
                    let (_loc_id,id) = id in
                    fun var  -> ((Some (id_loc id _loc_id)), var)));
           Decap.sequence opt_variance (Decap.char '_' '_')
             (fun var  _  -> (None, var))])
    let type_params = Decap.declare_grammar "type_params"
    let _ =
      Decap.set_grammar type_params
        (Decap.alternatives
           [Decap.apply (fun tp  -> [tp]) type_param;
           Decap.fsequence (Decap.string "(" "(")
             (Decap.fsequence type_param
                (Decap.sequence
                   (Decap.apply List.rev
                      (Decap.fixpoint []
                         (Decap.apply (fun x  y  -> x :: y)
                            (Decap.sequence (Decap.string "," ",") type_param
                               (fun _  tp  -> tp))))) (Decap.string ")" ")")
                   (fun tps  _  tp  _  -> tp :: tps)))])
    let type_equation = Decap.declare_grammar "type_equation"
    let _ =
      Decap.set_grammar type_equation
        (Decap.fsequence (Decap.char '=' '=')
           (Decap.sequence private_flag typexpr (fun p  te  _  -> (p, te))))
    let type_constraint = Decap.declare_grammar "type_constraint"
    let _ =
      Decap.set_grammar type_constraint
        (Decap.fsequence_position constraint_kw
           (Decap.fsequence (Decap.string "'" "'")
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) ident)
                 (Decap.sequence (Decap.char '=' '=') typexpr
                    (fun _  te  id  ->
                       let (_loc_id,id) = id in
                       fun _  _default_0  __loc__start__buf 
                         __loc__start__pos  __loc__end__buf  __loc__end__pos 
                         ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         ((loc_typ _loc_id (Ptyp_var id)), te, _loc))))))
    let constr_name2 = Decap.declare_grammar "constr_name2"
    let _ =
      Decap.set_grammar constr_name2
        (Decap.alternatives
           [constr_name;
           Decap.sequence (Decap.string "(" "(") (Decap.string ")" ")")
             (fun _  _  -> "()")])
    let constr_decl = Decap.declare_grammar "constr_decl"
    let _ =
      Decap.set_grammar constr_decl
        (Decap.sequence_position
           (Decap.apply_position
              (fun x  str  pos  str'  pos'  ->
                 ((locate str pos str' pos'), x)) constr_name2)
           (Decap.alternatives
              [Decap.apply
                 (fun te  ->
                    let tes =
                      match te with
                      | None  -> []
                      | Some { ptyp_desc = Ptyp_tuple tes; ptyp_loc = _ } ->
                          tes
                      | Some t -> [t] in
                    (tes, None))
                 (Decap.option None
                    (Decap.apply (fun x  -> Some x)
                       (Decap.sequence of_kw typexpr
                          (fun _  _default_0  -> _default_0))));
              Decap.fsequence (Decap.char ':' ':')
                (Decap.sequence
                   (Decap.option []
                      (Decap.fsequence
                         (typexpr_lvl (next_type_prio ProdType))
                         (Decap.sequence
                            (Decap.apply List.rev
                               (Decap.fixpoint []
                                  (Decap.apply (fun x  y  -> x :: y)
                                     (Decap.sequence (Decap.char '*' '*')
                                        (typexpr_lvl
                                           (next_type_prio ProdType))
                                        (fun _  _default_0  -> _default_0)))))
                            arrow_re (fun tes  _default_0  te  -> te :: tes))))
                   (typexpr_lvl (next_type_prio Arr))
                   (fun ats  te  _  -> (ats, (Some te))))])
           (fun cn  ->
              let (_loc_cn,cn) = cn in
              fun ((tes,te) as _default_0)  __loc__start__buf 
                __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                let c = id_loc cn _loc_cn in
                constructor_declaration
                  ~attributes:(attach_attrib ~local:true _loc []) _loc c tes
                  te))
    let field_decl = Decap.declare_grammar "field_decl"
    let _ =
      Decap.set_grammar field_decl
        (Decap.fsequence_position mutable_flag
           (Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) field_name)
              (Decap.sequence (Decap.string ":" ":") poly_typexpr
                 (fun _  pte  fn  ->
                    let (_loc_fn,fn) = fn in
                    fun m  __loc__start__buf  __loc__start__pos 
                      __loc__end__buf  __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      label_declaration _loc (id_loc fn _loc_fn) m pte))))
    let all_constr_decl = Decap.declare_grammar "all_constr_decl"
    let _ =
      Decap.set_grammar all_constr_decl
        (Decap.apply (fun cd  -> [cd]) constr_decl)
    let _ =
      set_grammar constr_decl_list
        (Decap.alternatives
           [Decap.fsequence
              (Decap.option None
                 (Decap.apply (fun x  -> Some x) (Decap.string "|" "|")))
              (Decap.sequence all_constr_decl
                 (Decap.apply List.rev
                    (Decap.fixpoint []
                       (Decap.apply (fun x  y  -> x :: y)
                          (Decap.sequence (Decap.string "|" "|")
                             all_constr_decl (fun _  cd  -> cd)))))
                 (fun cd  cds  _default_0  -> List.flatten (cd :: cds)));
           Decap.apply (fun _  -> []) (Decap.empty ())])
    let field_decl_aux = Decap.declare_grammar "field_decl_aux"
    let _ =
      Decap.set_grammar field_decl_aux
        (Decap.alternatives
           [Decap.apply (fun _  -> []) (Decap.empty ());
           Decap.fsequence field_decl_aux
             (Decap.sequence field_decl semi_col
                (fun fd  _default_0  fs  -> fd :: fs))])
    let _ =
      set_grammar field_decl_list
        (Decap.alternatives
           [Decap.apply (fun fs  -> List.rev fs) field_decl_aux;
           Decap.sequence field_decl_aux field_decl
             (fun fs  fd  -> List.rev (fd :: fs))])
    let type_representation = Decap.declare_grammar "type_representation"
    let _ =
      Decap.set_grammar type_representation
        (Decap.alternatives
           [Decap.fsequence (Decap.string "{" "{")
              (Decap.sequence field_decl_list (Decap.string "}" "}")
                 (fun fds  _  _  -> Ptype_record fds));
           Decap.apply
             (fun cds  ->
                if cds = []
                then give_up "Illegal empty constructors declaration";
                Ptype_variant cds) constr_decl_list])
    let type_information = Decap.declare_grammar "type_information"
    let _ =
      Decap.set_grammar type_information
        (Decap.fsequence
           (Decap.option None (Decap.apply (fun x  -> Some x) type_equation))
           (Decap.sequence
              (Decap.option None
                 (Decap.apply (fun x  -> Some x)
                    (Decap.fsequence (Decap.char '=' '=')
                       (Decap.sequence private_flag type_representation
                          (fun pri  tr  _  -> (pri, tr))))))
              (Decap.apply List.rev
                 (Decap.fixpoint []
                    (Decap.apply (fun x  y  -> x :: y) type_constraint)))
              (fun ptr  cstrs  te  ->
                 let (pri,tkind) =
                   match ptr with
                   | None  -> (Public, Ptype_abstract)
                   | Some c -> c in
                 (pri, te, tkind, cstrs))))
    let typedef_gen attach constr filter =
      Decap.fsequence_position (Decap.option [] type_params)
        (Decap.sequence
           (Decap.apply_position
              (fun x  str  pos  str'  pos'  ->
                 ((locate str pos str' pos'), x)) constr) type_information
           (fun tcn  ->
              let (_loc_tcn,tcn) = tcn in
              fun ti  tps  __loc__start__buf  __loc__start__pos 
                __loc__end__buf  __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                fun prev_loc  ->
                  let _loc =
                    match (prev_loc : Location.t option ) with
                    | None  -> _loc
                    | Some l -> merge2 l _loc in
                  let (pri,te,tkind,cstrs) = ti in
                  let (pri,te) =
                    match te with
                    | None  -> (pri, None)
                    | Some (Private ,te) ->
                        (if pri = Private then give_up "";
                         (Private, (Some te)))
                    | Some (_,te) -> (pri, (Some te)) in
                  ((id_loc tcn _loc_tcn),
                    (type_declaration
                       ~attributes:(if attach
                                    then attach_attrib _loc []
                                    else []) _loc
                       (id_loc (filter tcn) _loc_tcn) tps cstrs tkind pri te))))
    let typedef =
      apply (fun f  -> f None)
        (typedef_gen true typeconstr_name (fun x  -> x))
    let typedef_in_constraint = typedef_gen false typeconstr Longident.last
    let type_definition = Decap.declare_grammar "type_definition"
    let _ =
      Decap.set_grammar type_definition
        (Decap.fsequence type_kw
           (Decap.sequence typedef
              (Decap.apply List.rev
                 (Decap.fixpoint []
                    (Decap.apply (fun x  y  -> x :: y)
                       (Decap.sequence and_kw typedef
                          (fun _default_0  td  -> td)))))
              (fun td  tds  _default_0  -> td :: tds)))
    let exception_declaration = Decap.declare_grammar "exception_declaration"
    let _ =
      Decap.set_grammar exception_declaration
        (Decap.fsequence_position exception_kw
           (Decap.sequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) constr_name)
              (Decap.option None
                 (Decap.apply (fun x  -> Some x)
                    (Decap.sequence of_kw typexpr
                       (fun _  _default_0  -> _default_0))))
              (fun cn  ->
                 let (_loc_cn,cn) = cn in
                 fun te  _default_0  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   let tes =
                     match te with
                     | None  -> []
                     | Some { ptyp_desc = Ptyp_tuple tes; ptyp_loc = _ } ->
                         tes
                     | Some t -> [t] in
                   ((id_loc cn _loc_cn), tes, _loc))))
    let exception_definition = Decap.declare_grammar "exception_definition"
    let _ =
      Decap.set_grammar exception_definition
        (Decap.alternatives
           [Decap.fsequence exception_kw
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) constr_name)
                 (Decap.sequence (Decap.char '=' '=')
                    (Decap.apply_position
                       (fun x  str  pos  str'  pos'  ->
                          ((locate str pos str' pos'), x)) constr)
                    (fun _  c  ->
                       let (_loc_c,c) = c in
                       fun cn  ->
                         let (_loc_cn,cn) = cn in
                         fun _default_0  ->
                           let name = id_loc cn _loc_cn in
                           let ex = id_loc c _loc_c in
                           Pstr_exn_rebind (name, ex))));
           Decap.apply
             (fun ((name,ed,_loc') as _default_0)  ->
                Pstr_exception (name, ed)) exception_declaration])
    let class_field_spec = declare_grammar "class_field_spec"
    let class_body_type = declare_grammar "class_body_type"
    let virt_mut = Decap.declare_grammar "virt_mut"
    let _ =
      Decap.set_grammar virt_mut
        (Decap.alternatives
           [Decap.sequence virtual_flag mutable_flag (fun v  m  -> (v, m));
           Decap.sequence mutable_kw virtual_kw
             (fun _default_1  _default_0  -> (Virtual, Mutable))])
    let virt_priv = Decap.declare_grammar "virt_priv"
    let _ =
      Decap.set_grammar virt_priv
        (Decap.alternatives
           [Decap.sequence virtual_flag private_flag (fun v  p  -> (v, p));
           Decap.sequence private_kw virtual_kw
             (fun _default_1  _default_0  -> (Virtual, Private))])
    let _ =
      set_grammar class_field_spec
        (Decap.alternatives
           [Decap.sequence_position inherit_kw class_body_type
              (fun _default_0  cbt  __loc__start__buf  __loc__start__pos 
                 __loc__end__buf  __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 pctf_loc _loc (Pctf_inher cbt));
           Decap.fsequence_position val_kw
             (Decap.fsequence virt_mut
                (Decap.fsequence inst_var_name
                   (Decap.sequence (Decap.string ":" ":") typexpr
                      (fun _  te  ivn  ((vir,mut) as _default_0)  _default_1 
                         __loc__start__buf  __loc__start__pos 
                         __loc__end__buf  __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         pctf_loc _loc (Pctf_val (ivn, mut, vir, te))))));
           Decap.fsequence_position method_kw
             (Decap.fsequence virt_priv
                (Decap.fsequence method_name
                   (Decap.sequence (Decap.string ":" ":") poly_typexpr
                      (fun _  te  mn  ((v,pri) as _default_0)  _default_1 
                         __loc__start__buf  __loc__start__pos 
                         __loc__end__buf  __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         if v = Concrete
                         then pctf_loc _loc (Pctf_meth (mn, pri, te))
                         else pctf_loc _loc (Pctf_virt (mn, pri, te))))));
           Decap.fsequence_position constraint_kw
             (Decap.fsequence typexpr
                (Decap.sequence (Decap.char '=' '=') typexpr
                   (fun _  te'  te  _default_0  __loc__start__buf 
                      __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      pctf_loc _loc (Pctf_cstr (te, te')))))])
    let _ =
      set_grammar class_body_type
        (Decap.alternatives
           [Decap.fsequence_position object_kw
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x))
                    (Decap.option None
                       (Decap.apply (fun x  -> Some x)
                          (Decap.fsequence (Decap.string "(" "(")
                             (Decap.sequence typexpr (Decap.string ")" ")")
                                (fun te  _  _  -> te))))))
                 (Decap.sequence
                    (Decap.apply_position
                       (fun x  str  pos  str'  pos'  ->
                          ((locate str pos str' pos'), x))
                       (Decap.apply List.rev
                          (Decap.fixpoint []
                             (Decap.apply (fun x  y  -> x :: y)
                                class_field_spec)))) end_kw
                    (fun cfs  ->
                       let (_loc_cfs,cfs) = cfs in
                       fun _default_0  te  ->
                         let (_loc_te,te) = te in
                         fun _default_1  __loc__start__buf  __loc__start__pos
                            __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           let self =
                             match te with
                             | None  -> loc_typ _loc_te Ptyp_any
                             | Some t -> t in
                           let sign =
                             {
                               pcsig_self = self;
                               pcsig_fields = cfs;
                               pcsig_loc = (merge2 _loc_te _loc_cfs)
                             } in
                           pcty_loc _loc (Pcty_signature sign))));
           Decap.sequence_position
             (Decap.option []
                (Decap.fsequence (Decap.string "[" "[")
                   (Decap.fsequence typexpr
                      (Decap.sequence
                         (Decap.apply List.rev
                            (Decap.fixpoint []
                               (Decap.apply (fun x  y  -> x :: y)
                                  (Decap.sequence (Decap.string "," ",")
                                     typexpr (fun _  te  -> te)))))
                         (Decap.string "]" "]")
                         (fun tes  _  te  _  -> te :: tes)))))
             (Decap.apply_position
                (fun x  str  pos  str'  pos'  ->
                   ((locate str pos str' pos'), x)) classtype_path)
             (fun tes  ctp  ->
                let (_loc_ctp,ctp) = ctp in
                fun __loc__start__buf  __loc__start__pos  __loc__end__buf 
                  __loc__end__pos  ->
                  let _loc =
                    locate __loc__start__buf __loc__start__pos
                      __loc__end__buf __loc__end__pos in
                  let ctp = id_loc ctp _loc_ctp in
                  pcty_loc _loc (Pcty_constr (ctp, tes)))])
    let class_type = Decap.declare_grammar "class_type"
    let _ =
      Decap.set_grammar class_type
        (Decap.sequence_position
           (Decap.apply_position
              (fun x  str  pos  str'  pos'  ->
                 ((locate str pos str' pos'), x))
              (Decap.apply List.rev
                 (Decap.fixpoint []
                    (Decap.apply (fun x  y  -> x :: y)
                       (Decap.fsequence
                          (Decap.option None
                             (Decap.apply (fun x  -> Some x) maybe_opt_label))
                          (Decap.sequence (Decap.string ":" ":") typexpr
                             (fun _  te  l  -> (l, te)))))))) class_body_type
           (fun tes  ->
              let (_loc_tes,tes) = tes in
              fun cbt  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                let app acc (lab,te) =
                  match lab with
                  | None  -> pcty_loc _loc (Pcty_fun ("", te, acc))
                  | Some l ->
                      pcty_loc _loc
                        (Pcty_fun
                           (l,
                             (if (l.[0]) = '?'
                              then mkoption _loc_tes te
                              else te), acc)) in
                List.fold_left app cbt (List.rev tes)))
    let type_parameters = Decap.declare_grammar "type_parameters"
    let _ =
      Decap.set_grammar type_parameters
        (Decap.sequence type_param
           (Decap.apply List.rev
              (Decap.fixpoint []
                 (Decap.apply (fun x  y  -> x :: y)
                    (Decap.sequence (Decap.string "," ",") type_param
                       (fun _  i2  -> i2))))) (fun i1  l  -> i1 :: l))
    let class_spec = Decap.declare_grammar "class_spec"
    let _ =
      Decap.set_grammar class_spec
        (Decap.fsequence_position virtual_flag
           (Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x))
                 (Decap.option []
                    (Decap.fsequence (Decap.string "[" "[")
                       (Decap.sequence type_parameters (Decap.string "]" "]")
                          (fun params  _  _  -> params)))))
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) class_name)
                 (Decap.sequence (Decap.string ":" ":") class_type
                    (fun _  ct  cn  ->
                       let (_loc_cn,cn) = cn in
                       fun params  ->
                         let (_loc_params,params) = params in
                         fun v  __loc__start__buf  __loc__start__pos 
                           __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           class_type_declaration
                             ~attributes:(attach_attrib _loc []) _loc_params
                             _loc (id_loc cn _loc_cn) params v ct)))))
    let class_specification = Decap.declare_grammar "class_specification"
    let _ =
      Decap.set_grammar class_specification
        (Decap.sequence class_spec
           (Decap.apply List.rev
              (Decap.fixpoint []
                 (Decap.apply (fun x  y  -> x :: y)
                    (Decap.sequence and_kw class_spec
                       (fun _  _default_0  -> _default_0)))))
           (fun cs  css  -> cs :: css))
    let classtype_def = Decap.declare_grammar "classtype_def"
    let _ =
      Decap.set_grammar classtype_def
        (Decap.fsequence_position virtual_flag
           (Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x))
                 (Decap.option []
                    (Decap.fsequence (Decap.string "[" "[")
                       (Decap.sequence type_parameters (Decap.string "]" "]")
                          (fun tp  _  _  -> tp)))))
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) class_name)
                 (Decap.sequence (Decap.char '=' '=') class_body_type
                    (fun _  cbt  cn  ->
                       let (_loc_cn,cn) = cn in
                       fun params  ->
                         let (_loc_params,params) = params in
                         fun v  __loc__start__buf  __loc__start__pos 
                           __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           class_type_declaration
                             ~attributes:(attach_attrib _loc []) _loc_params
                             _loc (id_loc cn _loc_cn) params v cbt)))))
    let classtype_definition = Decap.declare_grammar "classtype_definition"
    let _ =
      Decap.set_grammar classtype_definition
        (Decap.fsequence type_kw
           (Decap.sequence classtype_def
              (Decap.apply List.rev
                 (Decap.fixpoint []
                    (Decap.apply (fun x  y  -> x :: y)
                       (Decap.sequence and_kw classtype_def
                          (fun _  _default_0  -> _default_0)))))
              (fun cd  cds  _default_0  -> cd :: cds)))
    let integer_litteral = Decap.declare_grammar "integer_litteral"
    let _ =
      Decap.set_grammar integer_litteral
        (Decap.apply
           (fun ((s,co) as _default_0)  ->
              match co with
              | None  -> const_int (int_of_string s)
              | Some 'l' -> const_int32 (Int32.of_string s)
              | Some 'L' -> const_int64 (Int64.of_string s)
              | Some 'n' -> const_nativeint (Nativeint.of_string s)
              | Some _ -> Decap.give_up "Invalid integer litteral suffix...")
           int_litteral)
    let constant = Decap.declare_grammar "constant"
    let _ =
      Decap.set_grammar constant
        (Decap.alternatives
           [Decap.apply (fun f  -> const_float f) float_litteral;
           Decap.apply (fun c  -> const_char c) char_litteral;
           Decap.apply (fun s  -> const_string s) string_litteral;
           Decap.apply (fun s  -> const_string s) regexp_litteral;
           integer_litteral])
    let neg_constant = Decap.declare_grammar "neg_constant"
    let _ =
      Decap.set_grammar neg_constant
        (Decap.alternatives
           [Decap.sequence
              (Decap.alternatives
                 [Decap.apply (fun _  -> ()) (Decap.char '-' '-');
                 Decap.apply (fun _  -> ()) (Decap.string "-." "-.")])
              float_litteral (fun _default_0  f  -> const_float ("-" ^ f));
           Decap.sequence (Decap.char '-' '-') integer_litteral
             (fun _  i  ->
                match i with
                | Const_int i -> const_int (- i)
                | Const_int32 i -> const_int32 (Int32.neg i)
                | Const_int64 i -> const_int64 (Int64.neg i)
                | Const_nativeint i -> const_nativeint (Nativeint.neg i)
                | _ -> assert false)])
    let (extra_patterns_grammar,extra_patterns_grammar__set__grammar) =
      Decap.grammar_family "extra_patterns_grammar"
    let _ =
      extra_patterns_grammar__set__grammar
        (fun lvl  -> alternatives (List.map (fun g  -> g lvl) extra_patterns))
    let _ =
      set_pattern_lvl
        (fun (as_ok,lvl)  ->
           Decap.alternatives ((extra_patterns_grammar (as_ok, lvl)) ::
             (let y = (pattern_lvl (false, (next_pat_prio lvl))) ::
                (let y =
                   let y =
                     let y =
                       let y =
                         let y =
                           let y =
                             let y =
                               let y =
                                 let y =
                                   let y =
                                     let y =
                                       let y =
                                         let y =
                                           let y =
                                             let y =
                                               let y =
                                                 let y =
                                                   let y =
                                                     let y =
                                                       let y =
                                                         let y =
                                                           let y =
                                                             let y =
                                                               let y =
                                                                 let y = [] in
                                                                 if
                                                                   lvl =
                                                                    ConsPat
                                                                 then
                                                                   (Decap.fsequence_position
                                                                    (pattern_lvl
                                                                    (true,
                                                                    (next_pat_prio
                                                                    ConsPat)))
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (Decap.string
                                                                    "::" "::"))
                                                                    (pattern_lvl
                                                                    (false,
                                                                    ConsPat))
                                                                    (fun c 
                                                                    ->
                                                                    let 
                                                                    (_loc_c,c)
                                                                    = c in
                                                                    fun p'  p
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let cons
                                                                    =
                                                                    id_loc
                                                                    (Lident
                                                                    "::")
                                                                    _loc_c in
                                                                    let args
                                                                    =
                                                                    loc_pat
                                                                    (ghost
                                                                    _loc)
                                                                    (Ppat_tuple
                                                                    [p; p']) in
                                                                    loc_pat
                                                                    _loc
                                                                    (ppat_construct
                                                                    (cons,
                                                                    (Some
                                                                    args))))))
                                                                   :: y
                                                                 else y in
                                                               if
                                                                 lvl = TupPat
                                                               then
                                                                 (Decap.sequence_position
                                                                    (
                                                                    Decap.apply
                                                                    List.rev
                                                                    (Decap.fixpoint1
                                                                    []
                                                                    (Decap.apply
                                                                    (fun x  y
                                                                     -> x ::
                                                                    y)
                                                                    (Decap.sequence
                                                                    (pattern_lvl
                                                                    (true,
                                                                    (next_pat_prio
                                                                    TupPat)))
                                                                    (Decap.char
                                                                    ',' ',')
                                                                    (fun
                                                                    _default_0
                                                                     _  ->
                                                                    _default_0)))))
                                                                    (
                                                                    pattern_lvl
                                                                    (false,
                                                                    (next_pat_prio
                                                                    TupPat)))
                                                                    (
                                                                    fun ps  p
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_pat
                                                                    _loc
                                                                    (Ppat_tuple
                                                                    (ps @ [p]))))
                                                                 :: y
                                                               else y in
                                                             if lvl = AltPat
                                                             then
                                                               (Decap.fsequence_position
                                                                  (pattern_lvl
                                                                    (true,
                                                                    AltPat))
                                                                  (Decap.sequence
                                                                    (Decap.char
                                                                    '|' '|')
                                                                    (pattern_lvl
                                                                    (false,
                                                                    (next_pat_prio
                                                                    AltPat)))
                                                                    (fun _ 
                                                                    p'  p 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_pat
                                                                    _loc
                                                                    (Ppat_or
                                                                    (p, p')))))
                                                               :: y
                                                             else y in
                                                           if lvl = AtomPat
                                                           then
                                                             (Decap.fsequence_position
                                                                (Decap.ignore_next_blank
                                                                   (Decap.char
                                                                    '$' '$'))
                                                                (Decap.fsequence
                                                                   (Decap.option
                                                                    "pat"
                                                                    (Decap.sequence
                                                                    (Decap.ignore_next_blank
                                                                    (Decap.regexp
                                                                    ~name:"[a-z]+"
                                                                    "[a-z]+"
                                                                    (fun
                                                                    groupe 
                                                                    ->
                                                                    groupe 0)))
                                                                    (Decap.char
                                                                    ':' ':')
                                                                    (fun
                                                                    _default_0
                                                                     _  ->
                                                                    _default_0)))
                                                                   (Decap.sequence
                                                                    (Decap.ignore_next_blank
                                                                    expression)
                                                                    (Decap.char
                                                                    '$' '$')
                                                                    (fun e  _
                                                                     aq  _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let open Quote in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let locate
                                                                    _loc e =
                                                                    quote_record
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    ((parsetree
                                                                    "ppat_desc"),
                                                                    e);
                                                                    ((parsetree
                                                                    "ppat_loc"),
                                                                    (quote_location_t
                                                                    e_loc
                                                                    _loc _loc))] in
                                                                    let generic_antiquote
                                                                    e =
                                                                    function
                                                                    | 
                                                                    Quote_ppat
                                                                     -> e
                                                                    | 
                                                                    _ ->
                                                                    failwith
                                                                    "invalid antiquotation type" in
                                                                    let f =
                                                                    match aq
                                                                    with
                                                                    | 
                                                                    "pat" ->
                                                                    generic_antiquote
                                                                    e
                                                                    | 
                                                                    "bool" ->
                                                                    let e =
                                                                    quote_const
                                                                    e_loc
                                                                    _loc
                                                                    (parsetree
                                                                    "Ppat_constant")
                                                                    [
                                                                    quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "const_bool")
                                                                    [e]] in
                                                                    generic_antiquote
                                                                    (locate
                                                                    _loc e)
                                                                    | 
                                                                    "int" ->
                                                                    let e =
                                                                    quote_const
                                                                    e_loc
                                                                    _loc
                                                                    (parsetree
                                                                    "Ppat_constant")
                                                                    [
                                                                    quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "const_int")
                                                                    [e]] in
                                                                    generic_antiquote
                                                                    (locate
                                                                    _loc e)
                                                                    | 
                                                                    "string"
                                                                    ->
                                                                    let e =
                                                                    quote_const
                                                                    e_loc
                                                                    _loc
                                                                    (parsetree
                                                                    "Ppat_constant")
                                                                    [
                                                                    quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "const_string")
                                                                    [e]] in
                                                                    generic_antiquote
                                                                    (locate
                                                                    _loc e)
                                                                    | 
                                                                    "list" ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "pat_list")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    "tuple"
                                                                    ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "pat_tuple")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    "array"
                                                                    ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "pat_array")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    _ ->
                                                                    give_up
                                                                    "bad antiquotation" in
                                                                    Quote.ppat_antiquotation
                                                                    _loc f))))
                                                             :: y
                                                           else y in
                                                         if lvl = AtomPat
                                                         then
                                                           (Decap.sequence
                                                              (Decap.ignore_next_blank
                                                                 (Decap.char
                                                                    '$' '$'))
                                                              uident
                                                              (fun _  c  ->
                                                                 try
                                                                   let str =
                                                                    Sys.getenv
                                                                    c in
                                                                   parse_string
                                                                    ~filename:(
                                                                    "ENV:" ^
                                                                    c)
                                                                    pattern
                                                                    ocaml_blank
                                                                    str
                                                                 with
                                                                 | Not_found 
                                                                    ->
                                                                    give_up
                                                                    ""))
                                                           :: y
                                                         else y in
                                                       if lvl = AtomPat
                                                       then
                                                         (Decap.fsequence_position
                                                            (Decap.char '('
                                                               '(')
                                                            (Decap.fsequence
                                                               module_kw
                                                               (Decap.fsequence
                                                                  (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_name)
                                                                  (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (Decap.option
                                                                    None
                                                                    (Decap.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Decap.sequence
                                                                    (Decap.string
                                                                    ":" ":")
                                                                    package_type
                                                                    (fun _ 
                                                                    pt  -> pt)))))
                                                                    (Decap.char
                                                                    ')' ')')
                                                                    (fun pt 
                                                                    ->
                                                                    let 
                                                                    (_loc_pt,pt)
                                                                    = pt in
                                                                    fun _  mn
                                                                     ->
                                                                    let 
                                                                    (_loc_mn,mn)
                                                                    = mn in
                                                                    fun
                                                                    _default_0
                                                                     _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let unpack
                                                                    =
                                                                    Ppat_unpack
                                                                    mn in
                                                                    let pat =
                                                                    match pt
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    unpack
                                                                    | 
                                                                    Some pt
                                                                    ->
                                                                    let pt =
                                                                    loc_typ
                                                                    _loc_pt
                                                                    pt in
                                                                    Ppat_constraint
                                                                    ((loc_pat
                                                                    _loc_mn
                                                                    unpack),
                                                                    pt) in
                                                                    loc_pat
                                                                    _loc pat)))))
                                                         :: y
                                                       else y in
                                                     if lvl = AtomPat
                                                     then
                                                       (Decap.sequence_position
                                                          begin_kw end_kw
                                                          (fun _default_1 
                                                             _default_0 
                                                             __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos
                                                              ->
                                                             let _loc =
                                                               locate
                                                                 __loc__start__buf
                                                                 __loc__start__pos
                                                                 __loc__end__buf
                                                                 __loc__end__pos in
                                                             let unt =
                                                               id_loc
                                                                 (Lident "()")
                                                                 _loc in
                                                             loc_pat _loc
                                                               (ppat_construct
                                                                  (unt, None))))
                                                       :: y
                                                     else y in
                                                   if lvl = AtomPat
                                                   then
                                                     (Decap.sequence_position
                                                        (Decap.string "(" "(")
                                                        (Decap.string ")" ")")
                                                        (fun _  _ 
                                                           __loc__start__buf 
                                                           __loc__start__pos 
                                                           __loc__end__buf 
                                                           __loc__end__pos 
                                                           ->
                                                           let _loc =
                                                             locate
                                                               __loc__start__buf
                                                               __loc__start__pos
                                                               __loc__end__buf
                                                               __loc__end__pos in
                                                           let unt =
                                                             id_loc
                                                               (Lident "()")
                                                               _loc in
                                                           loc_pat _loc
                                                             (ppat_construct
                                                                (unt, None))))
                                                     :: y
                                                   else y in
                                                 if lvl = AtomPat
                                                 then
                                                   (Decap.sequence_position
                                                      (Decap.string "[|" "[|")
                                                      (Decap.string "|]" "|]")
                                                      (fun _  _ 
                                                         __loc__start__buf 
                                                         __loc__start__pos 
                                                         __loc__end__buf 
                                                         __loc__end__pos  ->
                                                         let _loc =
                                                           locate
                                                             __loc__start__buf
                                                             __loc__start__pos
                                                             __loc__end__buf
                                                             __loc__end__pos in
                                                         loc_pat _loc
                                                           (Ppat_array [])))
                                                   :: y
                                                 else y in
                                               if lvl = AtomPat
                                               then
                                                 (Decap.fsequence_position
                                                    (Decap.string "[|" "[|")
                                                    (Decap.fsequence pattern
                                                       (Decap.fsequence
                                                          (Decap.apply
                                                             List.rev
                                                             (Decap.fixpoint
                                                                []
                                                                (Decap.apply
                                                                   (fun x  y 
                                                                    -> x :: y)
                                                                   (Decap.sequence
                                                                    semi_col
                                                                    pattern
                                                                    (fun
                                                                    _default_0
                                                                     p  -> p)))))
                                                          (Decap.sequence
                                                             (Decap.option
                                                                None
                                                                (Decap.apply
                                                                   (fun x  ->
                                                                    Some x)
                                                                   semi_col))
                                                             (Decap.string
                                                                "|]" "|]")
                                                             (fun _default_0 
                                                                _  ps  p  _ 
                                                                __loc__start__buf
                                                                 __loc__start__pos
                                                                 __loc__end__buf
                                                                 __loc__end__pos
                                                                 ->
                                                                let _loc =
                                                                  locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                loc_pat _loc
                                                                  (Ppat_array
                                                                    (p :: ps)))))))
                                                 :: y
                                               else y in
                                             if lvl = AtomPat
                                             then
                                               (Decap.sequence_position
                                                  (Decap.string "[" "[")
                                                  (Decap.string "]" "]")
                                                  (fun _  _ 
                                                     __loc__start__buf 
                                                     __loc__start__pos 
                                                     __loc__end__buf 
                                                     __loc__end__pos  ->
                                                     let _loc =
                                                       locate
                                                         __loc__start__buf
                                                         __loc__start__pos
                                                         __loc__end__buf
                                                         __loc__end__pos in
                                                     let nil =
                                                       id_loc (Lident "[]")
                                                         _loc in
                                                     loc_pat _loc
                                                       (ppat_construct
                                                          (nil, None))))
                                               :: y
                                             else y in
                                           if lvl = AtomPat
                                           then
                                             (Decap.fsequence_position
                                                (Decap.string "[" "[")
                                                (Decap.fsequence pattern
                                                   (Decap.fsequence
                                                      (Decap.apply List.rev
                                                         (Decap.fixpoint []
                                                            (Decap.apply
                                                               (fun x  y  ->
                                                                  x :: y)
                                                               (Decap.sequence
                                                                  semi_col
                                                                  pattern
                                                                  (fun
                                                                    _default_0
                                                                     p  -> p)))))
                                                      (Decap.sequence
                                                         (Decap.option None
                                                            (Decap.apply
                                                               (fun x  ->
                                                                  Some x)
                                                               semi_col))
                                                         (Decap.string "]"
                                                            "]")
                                                         (fun _default_0  _ 
                                                            ps  p  _ 
                                                            __loc__start__buf
                                                             __loc__start__pos
                                                             __loc__end__buf 
                                                            __loc__end__pos 
                                                            ->
                                                            let _loc =
                                                              locate
                                                                __loc__start__buf
                                                                __loc__start__pos
                                                                __loc__end__buf
                                                                __loc__end__pos in
                                                            pat_list _loc (p
                                                              :: ps))))))
                                             :: y
                                           else y in
                                         if lvl = AtomPat
                                         then
                                           (Decap.fsequence_position
                                              (Decap.char '{' '{')
                                              (Decap.fsequence
                                                 (Decap.apply_position
                                                    (fun x  str  pos  str' 
                                                       pos'  ->
                                                       ((locate str pos str'
                                                           pos'), x)) field)
                                                 (Decap.fsequence
                                                    (Decap.option None
                                                       (Decap.apply
                                                          (fun x  -> Some x)
                                                          (Decap.sequence
                                                             (Decap.char '='
                                                                '=') pattern
                                                             (fun _  p  -> p))))
                                                    (Decap.fsequence
                                                       (Decap.apply List.rev
                                                          (Decap.fixpoint []
                                                             (Decap.apply
                                                                (fun x  y  ->
                                                                   x :: y)
                                                                (Decap.fsequence
                                                                   semi_col
                                                                   (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x)) field)
                                                                    (Decap.option
                                                                    None
                                                                    (Decap.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Decap.sequence
                                                                    (Decap.char
                                                                    '=' '=')
                                                                    pattern
                                                                    (fun _  p
                                                                     -> p))))
                                                                    (fun f 
                                                                    ->
                                                                    let 
                                                                    (_loc_f,f)
                                                                    = f in
                                                                    fun p 
                                                                    _default_0
                                                                     ->
                                                                    ((id_loc
                                                                    f _loc_f),
                                                                    p)))))))
                                                       (Decap.fsequence
                                                          (Decap.option None
                                                             (Decap.apply
                                                                (fun x  ->
                                                                   Some x)
                                                                (Decap.sequence
                                                                   semi_col
                                                                   joker_kw
                                                                   (fun
                                                                    _default_1
                                                                     _default_0
                                                                     -> ()))))
                                                          (Decap.sequence
                                                             (Decap.option
                                                                None
                                                                (Decap.apply
                                                                   (fun x  ->
                                                                    Some x)
                                                                   semi_col))
                                                             (Decap.char '}'
                                                                '}')
                                                             (fun _default_0 
                                                                _  clsd  fps 
                                                                p  f  ->
                                                                let (_loc_f,f)
                                                                  = f in
                                                                fun s 
                                                                  __loc__start__buf
                                                                   __loc__start__pos
                                                                   __loc__end__buf
                                                                   __loc__end__pos
                                                                   ->
                                                                  let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                  let all =
                                                                    ((id_loc
                                                                    f _loc_f),
                                                                    p) :: fps in
                                                                  let f
                                                                    (lab,pat)
                                                                    =
                                                                    match pat
                                                                    with
                                                                    | 
                                                                    Some p ->
                                                                    (lab, p)
                                                                    | 
                                                                    None  ->
                                                                    let slab
                                                                    =
                                                                    match 
                                                                    lab.txt
                                                                    with
                                                                    | 
                                                                    Lident s
                                                                    ->
                                                                    id_loc s
                                                                    lab.loc
                                                                    | 
                                                                    _ ->
                                                                    give_up
                                                                    "" in
                                                                    (lab,
                                                                    (loc_pat
                                                                    lab.loc
                                                                    (Ppat_var
                                                                    slab))) in
                                                                  let all =
                                                                    List.map
                                                                    f all in
                                                                  let cl =
                                                                    match clsd
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    Closed
                                                                    | 
                                                                    Some _ ->
                                                                    Open in
                                                                  loc_pat
                                                                    _loc
                                                                    (
                                                                    Ppat_record
                                                                    (all, cl)))))))))
                                           :: y
                                         else y in
                                       if lvl = AtomPat
                                       then
                                         (Decap.sequence_position
                                            (Decap.char '#' '#')
                                            (Decap.apply_position
                                               (fun x  str  pos  str'  pos' 
                                                  ->
                                                  ((locate str pos str' pos'),
                                                    x)) typeconstr)
                                            (fun s  t  ->
                                               let (_loc_t,t) = t in
                                               fun __loc__start__buf 
                                                 __loc__start__pos 
                                                 __loc__end__buf 
                                                 __loc__end__pos  ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 loc_pat _loc
                                                   (Ppat_type
                                                      (id_loc t _loc_t))))
                                         :: y
                                       else y in
                                     if lvl = AtomPat
                                     then
                                       (Decap.apply_position
                                          (fun c  __loc__start__buf 
                                             __loc__start__pos 
                                             __loc__end__buf  __loc__end__pos
                                              ->
                                             let _loc =
                                               locate __loc__start__buf
                                                 __loc__start__pos
                                                 __loc__end__buf
                                                 __loc__end__pos in
                                             loc_pat _loc
                                               (Ppat_variant (c, None)))
                                          tag_name)
                                       :: y
                                     else y in
                                   if lvl = ConstrPat
                                   then
                                     (Decap.sequence_position tag_name
                                        (pattern_lvl (false, ConstrPat))
                                        (fun c  p  __loc__start__buf 
                                           __loc__start__pos  __loc__end__buf
                                            __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           loc_pat _loc
                                             (Ppat_variant (c, (Some p)))))
                                     :: y
                                   else y in
                                 if lvl = AtomPat
                                 then
                                   (Decap.apply_position
                                      (fun b  __loc__start__buf 
                                         __loc__start__pos  __loc__end__buf 
                                         __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         let fls = id_loc (Lident b) _loc in
                                         loc_pat _loc
                                           (ppat_construct (fls, None)))
                                      bool_lit)
                                   :: y
                                 else y in
                               if lvl = AtomPat
                               then
                                 (Decap.apply_position
                                    (fun c  ->
                                       let (_loc_c,c) = c in
                                       fun __loc__start__buf 
                                         __loc__start__pos  __loc__end__buf 
                                         __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         let ast =
                                           ppat_construct
                                             ((id_loc c _loc_c), None) in
                                         loc_pat _loc ast)
                                    (Decap.apply_position
                                       (fun x  str  pos  str'  pos'  ->
                                          ((locate str pos str' pos'), x))
                                       constr))
                                 :: y
                               else y in
                             if lvl = ConstrPat
                             then
                               (Decap.sequence_position
                                  (Decap.apply_position
                                     (fun x  str  pos  str'  pos'  ->
                                        ((locate str pos str' pos'), x))
                                     constr) (pattern_lvl (false, ConstrPat))
                                  (fun c  ->
                                     let (_loc_c,c) = c in
                                     fun p  __loc__start__buf 
                                       __loc__start__pos  __loc__end__buf 
                                       __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       let ast =
                                         ppat_construct
                                           ((id_loc c _loc_c), (Some p)) in
                                       loc_pat _loc ast))
                               :: y
                             else y in
                           if lvl = ConstrPat
                           then
                             (Decap.sequence_position lazy_kw
                                (pattern_lvl (false, ConstrPat))
                                (fun _default_0  p  __loc__start__buf 
                                   __loc__start__pos  __loc__end__buf 
                                   __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos in
                                   let ast = Ppat_lazy p in loc_pat _loc ast))
                             :: y
                           else y in
                         if lvl = AtomPat
                         then
                           (Decap.fsequence_position (Decap.char '(' '(')
                              (Decap.fsequence pattern
                                 (Decap.sequence
                                    (Decap.option None
                                       (Decap.apply (fun x  -> Some x)
                                          (Decap.sequence
                                             (Decap.char ':' ':') typexpr
                                             (fun _  _default_0  ->
                                                _default_0))))
                                    (Decap.char ')' ')')
                                    (fun ty  _  p  _  __loc__start__buf 
                                       __loc__start__pos  __loc__end__buf 
                                       __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       let p =
                                         match ty with
                                         | None  -> loc_pat _loc p.ppat_desc
                                         | Some ty ->
                                             loc_pat _loc
                                               (Ppat_constraint (p, ty)) in
                                       p))))
                           :: y
                         else y in
                       if lvl = AtomPat
                       then
                         (Decap.apply_position
                            (fun c  __loc__start__buf  __loc__start__pos 
                               __loc__end__buf  __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               loc_pat _loc (Ppat_constant c))
                            (Decap.alternatives [constant; neg_constant]))
                         :: y
                       else y in
                     if lvl = AtomPat
                     then
                       (Decap.fsequence_position char_litteral
                          (Decap.sequence (Decap.string ".." "..")
                             char_litteral
                             (fun _  c2  c1  __loc__start__buf 
                                __loc__start__pos  __loc__end__buf 
                                __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos in
                                let (ic1,ic2) =
                                  ((Char.code c1), (Char.code c2)) in
                                if ic1 > ic2 then assert false;
                                (let const i =
                                   Ppat_constant (const_char (Char.chr i)) in
                                 let rec range acc a b =
                                   if a > b
                                   then assert false
                                   else
                                     if a = b
                                     then a :: acc
                                     else range (a :: acc) (a + 1) b in
                                 let opts =
                                   List.map
                                     (fun i  -> loc_pat _loc (const i))
                                     (range [] ic1 ic2) in
                                 List.fold_left
                                   (fun acc  o  ->
                                      loc_pat _loc (Ppat_or (o, acc)))
                                   (List.hd opts) (List.tl opts)))))
                       :: y
                     else y in
                   if lvl = AtomPat
                   then
                     (Decap.apply_position
                        (fun _default_0  __loc__start__buf  __loc__start__pos
                            __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           loc_pat _loc Ppat_any) joker_kw)
                     :: y
                   else y in
                 if lvl = AtomPat
                 then
                   (Decap.apply_position
                      (fun vn  ->
                         let (_loc_vn,vn) = vn in
                         fun __loc__start__buf  __loc__start__pos 
                           __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           loc_pat _loc (Ppat_var (id_loc vn _loc_vn)))
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) value_name))
                   :: y
                 else y) in
              if as_ok
              then
                (Decap.fsequence_position (pattern_lvl (as_ok, lvl))
                   (Decap.sequence as_kw
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) value_name)
                      (fun _default_0  vn  ->
                         let (_loc_vn,vn) = vn in
                         fun p  __loc__start__buf  __loc__start__pos 
                           __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           loc_pat _loc (Ppat_alias (p, (id_loc vn _loc_vn))))))
                :: y
              else y)))
    let let_re = "\\(let\\)\\|\\(val\\)\\b"
    type assoc =  
      | NoAssoc
      | Left
      | Right 
    let assoc =
      function
      | Prefix |Dot |Dash |Opp  -> NoAssoc
      | Prod |Sum |Eq  -> Left
      | _ -> Right
    let infix_prio s =
      match s.[0] with
      | '*' ->
          if ((String.length s) > 1) && ((s.[1]) = '*') then Pow else Prod
      | '/'|'%' -> Prod
      | '+'|'-' -> Sum
      | ':' ->
          if ((String.length s) > 1) && ((s.[1]) = '=') then Aff else Cons
      | '<' -> if ((String.length s) > 1) && ((s.[1]) = '-') then Aff else Eq
      | '@'|'^' -> Append
      | '&' ->
          if
            ((String.length s) = 1) ||
              (((String.length s) = 2) && ((s.[1]) = '&'))
          then Conj
          else Eq
      | '|' ->
          if ((String.length s) = 2) && ((s.[1]) = '|') then Disj else Eq
      | '='|'>'|'$'|'!' -> Eq
      | 'o' -> Disj
      | 'm' -> Prod
      | 'a' -> Pow
      | 'l' -> (match s.[1] with | 's' -> Pow | _ -> Prod)
      | _ -> (Printf.printf "%s\n%!" s; assert false)
    let prefix_prio s =
      if (s = "-") || ((s = "-.") || ((s = "+") || (s = "+.")))
      then Opp
      else Prefix
    let array_function loc str name =
      let name = if !fast then "unsafe_" ^ name else name in
      loc_expr loc (Pexp_ident (id_loc (Ldot ((Lident str), name)) loc))
    let bigarray_function loc str name =
      let name = if !fast then "unsafe_" ^ name else name in
      let lid = Ldot ((Ldot ((Lident "Bigarray"), str)), name) in
      loc_expr loc (Pexp_ident (id_loc lid loc))
    let untuplify exp =
      match exp.pexp_desc with | Pexp_tuple es -> es | _ -> [exp]
    let bigarray_get loc arr arg =
      let get = if !fast then "unsafe_get" else "get" in
      match untuplify arg with
      | c1::[] ->
          exp_apply loc (bigarray_function loc "Array1" get) [arr; c1]
      | c1::c2::[] ->
          exp_apply loc (bigarray_function loc "Array2" get) [arr; c1; c2]
      | c1::c2::c3::[] ->
          exp_apply loc (bigarray_function loc "Array3" get)
            [arr; c1; c2; c3]
      | coords ->
          exp_apply loc (bigarray_function loc "Genarray" "get")
            [arr; loc_expr loc (Pexp_array coords)]
    let bigarray_set loc arr arg newval =
      let set = if !fast then "unsafe_set" else "set" in
      match untuplify arg with
      | c1::[] ->
          exp_apply loc (bigarray_function loc "Array1" set)
            [arr; c1; newval]
      | c1::c2::[] ->
          exp_apply loc (bigarray_function loc "Array2" set)
            [arr; c1; c2; newval]
      | c1::c2::c3::[] ->
          exp_apply loc (bigarray_function loc "Array3" set)
            [arr; c1; c2; c3; newval]
      | coords ->
          exp_apply loc (bigarray_function loc "Genarray" "set")
            [arr; loc_expr loc (Pexp_array coords); newval]
    let constructor = Decap.declare_grammar "constructor"
    let _ =
      Decap.set_grammar constructor
        (Decap.sequence
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence module_path (Decap.string "." ".")
                    (fun m  _  -> m))))
           (Decap.alternatives [uident; bool_lit])
           (fun m  id  ->
              match m with | None  -> Lident id | Some m -> Ldot (m, id)))
    let argument = Decap.declare_grammar "argument"
    let _ =
      Decap.set_grammar argument
        (Decap.alternatives
           [Decap.apply_position
              (fun id  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                 __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 ((labelled id),
                   (loc_expr _loc (Pexp_ident (id_loc (Lident id) _loc)))))
              label;
           Decap.sequence ty_label (expression_lvl (NoMatch, (next_exp App)))
             (fun id  e  -> (id, e));
           Decap.apply_position
             (fun id  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                ((optional id),
                  (loc_expr _loc (Pexp_ident (id_loc (Lident id) _loc)))))
             opt_label;
           Decap.sequence ty_opt_label
             (expression_lvl (NoMatch, (next_exp App)))
             (fun id  e  -> (id, e));
           Decap.apply (fun e  -> (nolabel, e))
             (expression_lvl (NoMatch, (next_exp App)))])
    let _ =
      set_parameter
        (fun allow_new_type  ->
           Decap.alternatives
             ((Decap.apply (fun pat  -> `Arg (nolabel, None, pat))
                 (pattern_lvl (false, AtomPat))) ::
             (Decap.fsequence_position (Decap.char '~' '~')
                (Decap.fsequence (Decap.char '(' '(')
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) lident)
                      (Decap.sequence
                         (Decap.option None
                            (Decap.apply (fun x  -> Some x)
                               (Decap.sequence (Decap.string ":" ":") typexpr
                                  (fun _  t  -> t)))) (Decap.string ")" ")")
                         (fun t  _  id  ->
                            let (_loc_id,id) = id in
                            fun _  _  __loc__start__buf  __loc__start__pos 
                              __loc__end__buf  __loc__end__pos  ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              let pat =
                                loc_pat _loc_id
                                  (Ppat_var (id_loc id _loc_id)) in
                              let pat =
                                match t with
                                | None  -> pat
                                | Some t ->
                                    loc_pat _loc (Ppat_constraint (pat, t)) in
                              `Arg ((labelled id), None, pat)))))) ::
             (Decap.sequence ty_label pattern
                (fun id  pat  -> `Arg (id, None, pat))) ::
             (Decap.fsequence (Decap.char '~' '~')
                (Decap.sequence
                   (Decap.apply_position
                      (fun x  str  pos  str'  pos'  ->
                         ((locate str pos str' pos'), x)) ident) no_colon
                   (fun id  ->
                      let (_loc_id,id) = id in
                      fun _default_0  _  ->
                        `Arg
                          ((labelled id), None,
                            (loc_pat _loc_id (Ppat_var (id_loc id _loc_id)))))))
             ::
             (Decap.fsequence (Decap.char '?' '?')
                (Decap.fsequence (Decap.char '(' '(')
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) lident)
                      (Decap.fsequence
                         (Decap.apply_position
                            (fun x  str  pos  str'  pos'  ->
                               ((locate str pos str' pos'), x))
                            (Decap.option None
                               (Decap.apply (fun x  -> Some x)
                                  (Decap.sequence (Decap.char ':' ':')
                                     typexpr (fun _  t  -> t)))))
                         (Decap.sequence
                            (Decap.option None
                               (Decap.apply (fun x  -> Some x)
                                  (Decap.sequence (Decap.char '=' '=')
                                     expression (fun _  e  -> e))))
                            (Decap.char ')' ')')
                            (fun e  _  t  ->
                               let (_loc_t,t) = t in
                               fun id  ->
                                 let (_loc_id,id) = id in
                                 fun _  _  ->
                                   let pat =
                                     loc_pat _loc_id
                                       (Ppat_var (id_loc id _loc_id)) in
                                   let pat =
                                     match t with
                                     | None  -> pat
                                     | Some t ->
                                         loc_pat (merge2 _loc_id _loc_t)
                                           (Ppat_constraint (pat, t)) in
                                   `Arg ((optional id), e, pat))))))) ::
             (Decap.fsequence ty_opt_label
                (Decap.fsequence (Decap.string "(" "(")
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) pattern)
                      (Decap.fsequence
                         (Decap.apply_position
                            (fun x  str  pos  str'  pos'  ->
                               ((locate str pos str' pos'), x))
                            (Decap.option None
                               (Decap.apply (fun x  -> Some x)
                                  (Decap.sequence (Decap.char ':' ':')
                                     typexpr (fun _  t  -> t)))))
                         (Decap.sequence
                            (Decap.option None
                               (Decap.apply (fun x  -> Some x)
                                  (Decap.sequence (Decap.char '=' '=')
                                     expression (fun _  e  -> e))))
                            (Decap.char ')' ')')
                            (fun e  _  t  ->
                               let (_loc_t,t) = t in
                               fun pat  ->
                                 let (_loc_pat,pat) = pat in
                                 fun _  id  ->
                                   let pat =
                                     match t with
                                     | None  -> pat
                                     | Some t ->
                                         loc_pat (merge2 _loc_pat _loc_t)
                                           (Ppat_constraint (pat, t)) in
                                   `Arg (id, e, pat))))))) ::
             (Decap.sequence ty_opt_label pattern
                (fun id  pat  -> `Arg (id, None, pat))) ::
             (Decap.apply
                (fun id  ->
                   let (_loc_id,id) = id in
                   `Arg
                     ((optional id), None,
                       (loc_pat _loc_id (Ppat_var (id_loc id _loc_id)))))
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x)) opt_label)) ::
             (let y = [] in
              if allow_new_type
              then
                (Decap.fsequence (Decap.char '(' '(')
                   (Decap.fsequence type_kw
                      (Decap.sequence typeconstr_name (Decap.char ')' ')')
                         (fun name  _  _default_0  _  -> `Type name))))
                :: y
              else y)))
    let apply_params ?(gh= false)  params e =
      let f acc =
        function
        | (`Arg (lbl,opt,pat),_loc') ->
            loc_expr (ghost (merge2 _loc' e.pexp_loc))
              (pexp_fun (lbl, opt, pat, acc))
        | (`Type name,_loc') ->
            loc_expr (ghost (merge2 _loc' e.pexp_loc))
              (Pexp_newtype (name, acc)) in
      let e = List.fold_left f e (List.rev params) in
      if gh then e else de_ghost e
    let apply_params_cls _loc params e =
      let f acc =
        function
        | `Arg (lbl,opt,pat) -> loc_pcl _loc (Pcl_fun (lbl, opt, pat, acc))
        | `Type name -> assert false in
      List.fold_left f e (List.rev params)
    let right_member = Decap.declare_grammar "right_member"
    let _ =
      Decap.set_grammar right_member
        (Decap.fsequence_position
           (Decap.apply List.rev
              (Decap.fixpoint1 []
                 (Decap.apply (fun x  y  -> x :: y)
                    (Decap.apply
                       (fun lb  -> let (_loc_lb,lb) = lb in (lb, _loc_lb))
                       (Decap.apply_position
                          (fun x  str  pos  str'  pos'  ->
                             ((locate str pos str' pos'), x))
                          (parameter true))))))
           (Decap.fsequence
              (Decap.option None
                 (Decap.apply (fun x  -> Some x)
                    (Decap.sequence (Decap.char ':' ':') typexpr
                       (fun _  t  -> t))))
              (Decap.sequence (Decap.char '=' '=') expression
                 (fun _  e  ty  l  __loc__start__buf  __loc__start__pos 
                    __loc__end__buf  __loc__end__pos  ->
                    let _loc =
                      locate __loc__start__buf __loc__start__pos
                        __loc__end__buf __loc__end__pos in
                    let e =
                      match ty with
                      | None  -> e
                      | Some ty ->
                          loc_expr (ghost _loc) (pexp_constraint (e, ty)) in
                    apply_params ~gh:true l e))))
    let eright_member = Decap.declare_grammar "eright_member"
    let _ =
      Decap.set_grammar eright_member
        (Decap.fsequence_position
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.sequence (Decap.char ':' ':') typexpr
                    (fun _  t  -> t))))
           (Decap.sequence (Decap.char '=' '=') expression
              (fun _  e  ty  __loc__start__buf  __loc__start__pos 
                 __loc__end__buf  __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 let e =
                   match ty with
                   | None  -> e
                   | Some ty ->
                       loc_expr (ghost _loc) (pexp_constraint (e, ty)) in
                 e)))
    let _ =
      set_grammar let_binding
        (Decap.alternatives
           [Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) pattern)
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) eright_member)
                 (Decap.sequence post_item_attributes
                    (Decap.option []
                       (Decap.sequence and_kw let_binding
                          (fun _  _default_0  -> _default_0)))
                    (fun a  l  e  ->
                       let (_loc_e,e) = e in
                       fun pat  ->
                         let (_loc_pat,pat) = pat in
                         let loc = merge2 _loc_pat _loc_e in
                         (value_binding ~attributes:(attach_attrib loc a) loc
                            pat e)
                           :: l)));
           Decap.fsequence
             (Decap.apply_position
                (fun x  str  pos  str'  pos'  ->
                   ((locate str pos str' pos'), x)) value_name)
             (Decap.fsequence
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x)) right_member)
                (Decap.sequence post_item_attributes
                   (Decap.option []
                      (Decap.sequence and_kw let_binding
                         (fun _  _default_0  -> _default_0)))
                   (fun a  l  e  ->
                      let (_loc_e,e) = e in
                      fun vn  ->
                        let (_loc_vn,vn) = vn in
                        let loc = merge2 _loc_vn _loc_e in
                        let pat = pat_ident _loc_vn vn in
                        (value_binding ~attributes:(attach_attrib loc a) loc
                           pat e)
                          :: l)));
           Decap.fsequence_position
             (Decap.apply_position
                (fun x  str  pos  str'  pos'  ->
                   ((locate str pos str' pos'), x)) value_name)
             (Decap.fsequence (Decap.char ':' ':')
                (Decap.fsequence only_poly_typexpr
                   (Decap.fsequence (Decap.char '=' '=')
                      (Decap.fsequence
                         (Decap.apply_position
                            (fun x  str  pos  str'  pos'  ->
                               ((locate str pos str' pos'), x)) expression)
                         (Decap.sequence post_item_attributes
                            (Decap.option []
                               (Decap.sequence and_kw let_binding
                                  (fun _  _default_0  -> _default_0)))
                            (fun a  l  e  ->
                               let (_loc_e,e) = e in
                               fun _  ty  _  vn  ->
                                 let (_loc_vn,vn) = vn in
                                 fun __loc__start__buf  __loc__start__pos 
                                   __loc__end__buf  __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos in
                                   let pat =
                                     loc_pat _loc
                                       (Ppat_constraint
                                          ((loc_pat _loc
                                              (Ppat_var (id_loc vn _loc_vn))),
                                            ty)) in
                                   let loc = merge2 _loc_vn _loc_e in
                                   (value_binding
                                      ~attributes:(attach_attrib loc a) loc
                                      pat e)
                                     :: l))))));
           Decap.fsequence_position
             (Decap.apply_position
                (fun x  str  pos  str'  pos'  ->
                   ((locate str pos str' pos'), x)) value_name)
             (Decap.fsequence (Decap.char ':' ':')
                (Decap.fsequence poly_syntax_typexpr
                   (Decap.fsequence (Decap.char '=' '=')
                      (Decap.fsequence
                         (Decap.apply_position
                            (fun x  str  pos  str'  pos'  ->
                               ((locate str pos str' pos'), x)) expression)
                         (Decap.sequence post_item_attributes
                            (Decap.option []
                               (Decap.sequence and_kw let_binding
                                  (fun _  _default_0  -> _default_0)))
                            (fun a  l  e  ->
                               let (_loc_e,e) = e in
                               fun _  ((ids,ty) as _default_0)  _  vn  ->
                                 let (_loc_vn,vn) = vn in
                                 fun __loc__start__buf  __loc__start__pos 
                                   __loc__end__buf  __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos in
                                   let (e,ty) =
                                     wrap_type_annotation _loc ids ty e in
                                   let pat =
                                     loc_pat _loc
                                       (Ppat_constraint
                                          ((loc_pat _loc
                                              (Ppat_var (id_loc vn _loc_vn))),
                                            ty)) in
                                   let loc = merge2 _loc_vn _loc_e in
                                   (value_binding
                                      ~attributes:(attach_attrib loc a) loc
                                      pat e)
                                     :: l))))))])
    let (match_case,match_case__set__grammar) =
      Decap.grammar_family "match_case"
    let _ =
      match_case__set__grammar
        (fun c  ->
           Decap.fsequence pattern
             (Decap.fsequence
                (Decap.option None
                   (Decap.apply (fun x  -> Some x)
                      (Decap.sequence when_kw expression
                         (fun _  _default_0  -> _default_0))))
                (Decap.sequence arrow_re (expression_lvl c)
                   (fun _default_0  e  w  pat  -> make_case pat e w))))
    let _ =
      set_grammar match_cases
        (Decap.alternatives
           [Decap.fsequence
              (Decap.option None
                 (Decap.apply (fun x  -> Some x) (Decap.char '|' '|')))
              (Decap.fsequence
                 (Decap.apply List.rev
                    (Decap.fixpoint []
                       (Decap.apply (fun x  y  -> x :: y)
                          (Decap.sequence (match_case (Let, Seq))
                             (Decap.char '|' '|')
                             (fun _default_0  _  -> _default_0)))))
                 (Decap.sequence (match_case (Match, Seq)) no_semi
                    (fun x  _default_0  l  _default_1  -> l @ [x])));
           Decap.apply (fun _  -> []) (Decap.empty ())])
    let type_coercion = Decap.declare_grammar "type_coercion"
    let _ =
      Decap.set_grammar type_coercion
        (Decap.alternatives
           [Decap.fsequence (Decap.string ":" ":")
              (Decap.sequence typexpr
                 (Decap.option None
                    (Decap.apply (fun x  -> Some x)
                       (Decap.sequence (Decap.string ":>" ":>") typexpr
                          (fun _  t'  -> t'))))
                 (fun t  t'  _  -> ((Some t), t')));
           Decap.sequence (Decap.string ":>" ":>") typexpr
             (fun _  t'  -> (None, (Some t')))])
    let expression_list = Decap.declare_grammar "expression_list"
    let _ =
      Decap.set_grammar expression_list
        (Decap.alternatives
           [Decap.fsequence
              (Decap.apply List.rev
                 (Decap.fixpoint []
                    (Decap.apply (fun x  y  -> x :: y)
                       (Decap.sequence
                          (Decap.apply_position
                             (fun x  str  pos  str'  pos'  ->
                                ((locate str pos str' pos'), x))
                             (expression_lvl (LetRight, (next_exp Seq))))
                          semi_col
                          (fun e  ->
                             let (_loc_e,e) = e in fun _  -> (e, _loc_e))))))
              (Decap.sequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x))
                    (expression_lvl (Match, (next_exp Seq))))
                 (Decap.option None (Decap.apply (fun x  -> Some x) semi_col))
                 (fun e  ->
                    let (_loc_e,e) = e in
                    fun _default_0  l  -> l @ [(e, _loc_e)]));
           Decap.apply (fun _  -> []) (Decap.empty ())])
    let record_item = Decap.declare_grammar "record_item"
    let _ =
      Decap.set_grammar record_item
        (Decap.alternatives
           [Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) field)
              (Decap.sequence (Decap.char '=' '=')
                 (expression_lvl (LetRight, (next_exp Seq)))
                 (fun _  e  f  ->
                    let (_loc_f,f) = f in ((id_loc f _loc_f), e)));
           Decap.apply
             (fun f  ->
                let (_loc_f,f) = f in
                let id = id_loc (Lident f) _loc_f in
                (id, (loc_expr _loc_f (Pexp_ident id))))
             (Decap.apply_position
                (fun x  str  pos  str'  pos'  ->
                   ((locate str pos str' pos'), x)) lident)])
    let last_record_item = Decap.declare_grammar "last_record_item"
    let _ =
      Decap.set_grammar last_record_item
        (Decap.alternatives
           [Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) field)
              (Decap.sequence (Decap.char '=' '=')
                 (expression_lvl (Match, (next_exp Seq)))
                 (fun _  e  f  ->
                    let (_loc_f,f) = f in ((id_loc f _loc_f), e)));
           Decap.apply
             (fun f  ->
                let (_loc_f,f) = f in
                let id = id_loc (Lident f) _loc_f in
                (id, (loc_expr _loc_f (Pexp_ident id))))
             (Decap.apply_position
                (fun x  str  pos  str'  pos'  ->
                   ((locate str pos str' pos'), x)) lident)])
    let _ =
      set_grammar record_list
        (Decap.alternatives
           [Decap.fsequence
              (Decap.apply List.rev
                 (Decap.fixpoint []
                    (Decap.apply (fun x  y  -> x :: y)
                       (Decap.sequence record_item semi_col
                          (fun _default_0  _  -> _default_0)))))
              (Decap.sequence last_record_item
                 (Decap.option None (Decap.apply (fun x  -> Some x) semi_col))
                 (fun it  _default_0  l  -> l @ [it]));
           Decap.apply (fun _  -> []) (Decap.empty ())])
    let obj_item = Decap.declare_grammar "obj_item"
    let _ =
      Decap.set_grammar obj_item
        (Decap.fsequence
           (Decap.apply_position
              (fun x  str  pos  str'  pos'  ->
                 ((locate str pos str' pos'), x)) inst_var_name)
           (Decap.sequence (Decap.char '=' '=')
              (expression_lvl (Match, (next_exp Seq)))
              (fun _  e  v  -> let (_loc_v,v) = v in ((id_loc v _loc_v), e))))
    let class_expr_base = Decap.declare_grammar "class_expr_base"
    let _ =
      Decap.set_grammar class_expr_base
        (Decap.alternatives
           [Decap.apply_position
              (fun cp  ->
                 let (_loc_cp,cp) = cp in
                 fun __loc__start__buf  __loc__start__pos  __loc__end__buf 
                   __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   let cp = id_loc cp _loc_cp in
                   loc_pcl _loc (Pcl_constr (cp, [])))
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) class_path);
           Decap.fsequence_position (Decap.char '[' '[')
             (Decap.fsequence typexpr
                (Decap.fsequence
                   (Decap.apply List.rev
                      (Decap.fixpoint []
                         (Decap.apply (fun x  y  -> x :: y)
                            (Decap.sequence (Decap.char ',' ',') typexpr
                               (fun _  te  -> te)))))
                   (Decap.sequence (Decap.char ']' ']')
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) class_path)
                      (fun _  cp  ->
                         let (_loc_cp,cp) = cp in
                         fun tes  te  _  __loc__start__buf  __loc__start__pos
                            __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           let cp = id_loc cp _loc_cp in
                           loc_pcl _loc (Pcl_constr (cp, (te :: tes)))))));
           Decap.fsequence_position (Decap.string "(" "(")
             (Decap.sequence class_expr (Decap.string ")" ")")
                (fun ce  _  _  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   loc_pcl _loc ce.pcl_desc));
           Decap.fsequence_position (Decap.string "(" "(")
             (Decap.fsequence class_expr
                (Decap.fsequence (Decap.string ":" ":")
                   (Decap.sequence class_type (Decap.string ")" ")")
                      (fun ct  _  _  ce  _  __loc__start__buf 
                         __loc__start__pos  __loc__end__buf  __loc__end__pos 
                         ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         loc_pcl _loc (Pcl_constraint (ce, ct))))));
           Decap.fsequence_position fun_kw
             (Decap.fsequence
                (Decap.apply List.rev
                   (Decap.fixpoint1 []
                      (Decap.apply (fun x  y  -> x :: y) (parameter false))))
                (Decap.sequence arrow_re class_expr
                   (fun _default_0  ce  ps  _default_1  __loc__start__buf 
                      __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      apply_params_cls _loc ps ce)));
           Decap.fsequence_position let_kw
             (Decap.fsequence rec_flag
                (Decap.fsequence let_binding
                   (Decap.sequence in_kw class_expr
                      (fun _default_0  ce  lbs  r  _default_1 
                         __loc__start__buf  __loc__start__pos 
                         __loc__end__buf  __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         loc_pcl _loc (Pcl_let (r, lbs, ce))))));
           Decap.fsequence_position object_kw
             (Decap.sequence class_body end_kw
                (fun cb  _default_0  _default_1  __loc__start__buf 
                   __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   loc_pcl _loc (Pcl_structure cb)))])
    let _ =
      set_grammar class_expr
        (Decap.sequence_position class_expr_base
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.apply List.rev
                    (Decap.fixpoint1 []
                       (Decap.apply (fun x  y  -> x :: y) argument)))))
           (fun ce  args  __loc__start__buf  __loc__start__pos 
              __loc__end__buf  __loc__end__pos  ->
              let _loc =
                locate __loc__start__buf __loc__start__pos __loc__end__buf
                  __loc__end__pos in
              match args with
              | None  -> ce
              | Some l -> loc_pcl _loc (Pcl_apply (ce, l))))
    let class_field = Decap.declare_grammar "class_field"
    let _ =
      Decap.set_grammar class_field
        (Decap.alternatives
           [Decap.fsequence_position inherit_kw
              (Decap.fsequence override_flag
                 (Decap.sequence class_expr
                    (Decap.option None
                       (Decap.apply (fun x  -> Some x)
                          (Decap.sequence as_kw lident
                             (fun _  _default_0  -> _default_0))))
                    (fun ce  id  o  _default_0  __loc__start__buf 
                       __loc__start__pos  __loc__end__buf  __loc__end__pos 
                       ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos in
                       loc_pcf _loc (Pcf_inher (o, ce, id)))));
           Decap.fsequence_position val_kw
             (Decap.fsequence override_flag
                (Decap.fsequence mutable_flag
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) inst_var_name)
                      (Decap.fsequence
                         (Decap.apply_position
                            (fun x  str  pos  str'  pos'  ->
                               ((locate str pos str' pos'), x))
                            (Decap.option None
                               (Decap.apply (fun x  -> Some x)
                                  (Decap.sequence (Decap.char ':' ':')
                                     typexpr (fun _  t  -> t)))))
                         (Decap.sequence (Decap.char '=' '=') expression
                            (fun _  e  te  ->
                               let (_loc_te,te) = te in
                               fun ivn  ->
                                 let (_loc_ivn,ivn) = ivn in
                                 fun m  o  _default_0  __loc__start__buf 
                                   __loc__start__pos  __loc__end__buf 
                                   __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos in
                                   let ivn = id_loc ivn _loc_ivn in
                                   let ex =
                                     match te with
                                     | None  -> e
                                     | Some t ->
                                         loc_expr _loc_te
                                           (pexp_constraint (e, t)) in
                                   loc_pcf _loc (Pcf_val (ivn, m, o, ex))))))));
           Decap.fsequence_position val_kw
             (Decap.fsequence mutable_flag
                (Decap.fsequence virtual_kw
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) inst_var_name)
                      (Decap.sequence (Decap.string ":" ":") typexpr
                         (fun _  te  ivn  ->
                            let (_loc_ivn,ivn) = ivn in
                            fun _default_0  m  _default_1  __loc__start__buf 
                              __loc__start__pos  __loc__end__buf 
                              __loc__end__pos  ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              let ivn = id_loc ivn _loc_ivn in
                              loc_pcf _loc (Pcf_valvirt (ivn, m, te)))))));
           Decap.fsequence_position val_kw
             (Decap.fsequence virtual_kw
                (Decap.fsequence mutable_kw
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) inst_var_name)
                      (Decap.sequence (Decap.string ":" ":") typexpr
                         (fun _  te  ivn  ->
                            let (_loc_ivn,ivn) = ivn in
                            fun _default_0  _default_1  _default_2 
                              __loc__start__buf  __loc__start__pos 
                              __loc__end__buf  __loc__end__pos  ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              let ivn = id_loc ivn _loc_ivn in
                              loc_pcf _loc (Pcf_valvirt (ivn, Mutable, te)))))));
           Decap.fsequence_position method_kw
             (Decap.fsequence override_flag
                (Decap.fsequence private_flag
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) method_name)
                      (Decap.fsequence (Decap.string ":" ":")
                         (Decap.fsequence poly_typexpr
                            (Decap.sequence (Decap.char '=' '=') expression
                               (fun _  e  te  _  mn  ->
                                  let (_loc_mn,mn) = mn in
                                  fun p  o  _default_0  __loc__start__buf 
                                    __loc__start__pos  __loc__end__buf 
                                    __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    let mn = id_loc mn _loc_mn in
                                    let e =
                                      loc_expr _loc
                                        (Pexp_poly (e, (Some te))) in
                                    loc_pcf _loc (Pcf_meth (mn, p, o, e)))))))));
           Decap.fsequence_position method_kw
             (Decap.fsequence override_flag
                (Decap.fsequence private_flag
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) method_name)
                      (Decap.fsequence (Decap.string ":" ":")
                         (Decap.fsequence poly_syntax_typexpr
                            (Decap.sequence (Decap.char '=' '=') expression
                               (fun _  e  ((ids,te) as _default_0)  _  mn  ->
                                  let (_loc_mn,mn) = mn in
                                  fun p  o  _default_1  __loc__start__buf 
                                    __loc__start__pos  __loc__end__buf 
                                    __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    let mn = id_loc mn _loc_mn in
                                    let (e,poly) =
                                      wrap_type_annotation _loc ids te e in
                                    let e =
                                      loc_expr _loc
                                        (Pexp_poly (e, (Some poly))) in
                                    loc_pcf _loc (Pcf_meth (mn, p, o, e)))))))));
           Decap.fsequence_position method_kw
             (Decap.fsequence override_flag
                (Decap.fsequence private_flag
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) method_name)
                      (Decap.fsequence
                         (Decap.apply List.rev
                            (Decap.fixpoint []
                               (Decap.apply (fun x  y  -> x :: y)
                                  (Decap.apply
                                     (fun p  ->
                                        let (_loc_p,p) = p in (p, _loc_p))
                                     (Decap.apply_position
                                        (fun x  str  pos  str'  pos'  ->
                                           ((locate str pos str' pos'), x))
                                        (parameter true))))))
                         (Decap.fsequence
                            (Decap.option None
                               (Decap.apply (fun x  -> Some x)
                                  (Decap.sequence (Decap.string ":" ":")
                                     typexpr (fun _  te  -> te))))
                            (Decap.sequence (Decap.char '=' '=') expression
                               (fun _  e  te  ps  mn  ->
                                  let (_loc_mn,mn) = mn in
                                  fun p  o  _default_0  __loc__start__buf 
                                    __loc__start__pos  __loc__end__buf 
                                    __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    if (ps = []) && (te <> None)
                                    then give_up "";
                                    (let mn = id_loc mn _loc_mn in
                                     let e =
                                       match te with
                                       | None  -> e
                                       | Some te ->
                                           loc_expr _loc
                                             (pexp_constraint (e, te)) in
                                     let e: expression = apply_params ps e in
                                     let e =
                                       loc_expr _loc (Pexp_poly (e, None)) in
                                     loc_pcf _loc (Pcf_meth (mn, p, o, e))))))))));
           Decap.fsequence_position method_kw
             (Decap.fsequence private_flag
                (Decap.fsequence virtual_kw
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) method_name)
                      (Decap.sequence (Decap.string ":" ":") poly_typexpr
                         (fun _  pte  mn  ->
                            let (_loc_mn,mn) = mn in
                            fun _default_0  p  _default_1  __loc__start__buf 
                              __loc__start__pos  __loc__end__buf 
                              __loc__end__pos  ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              let mn = id_loc mn _loc_mn in
                              loc_pcf _loc (Pcf_virt (mn, p, pte)))))));
           Decap.fsequence_position method_kw
             (Decap.fsequence virtual_kw
                (Decap.fsequence private_kw
                   (Decap.fsequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x)) method_name)
                      (Decap.sequence (Decap.string ":" ":") poly_typexpr
                         (fun _  pte  mn  ->
                            let (_loc_mn,mn) = mn in
                            fun _default_0  _default_1  _default_2 
                              __loc__start__buf  __loc__start__pos 
                              __loc__end__buf  __loc__end__pos  ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              let mn = id_loc mn _loc_mn in
                              loc_pcf _loc (Pcf_virt (mn, Private, pte)))))));
           Decap.fsequence_position constraint_kw
             (Decap.fsequence typexpr
                (Decap.sequence (Decap.char '=' '=') typexpr
                   (fun _  te'  te  _default_0  __loc__start__buf 
                      __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      loc_pcf _loc (Pcf_constr (te, te')))));
           Decap.sequence_position initializer_kw expression
             (fun _default_0  e  __loc__start__buf  __loc__start__pos 
                __loc__end__buf  __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_pcf _loc (Pcf_init e))])
    let _ =
      set_grammar class_body
        (Decap.sequence
           (Decap.apply_position
              (fun x  str  pos  str'  pos'  ->
                 ((locate str pos str' pos'), x))
              (Decap.option None (Decap.apply (fun x  -> Some x) pattern)))
           (Decap.apply List.rev
              (Decap.fixpoint []
                 (Decap.apply (fun x  y  -> x :: y) class_field)))
           (fun p  ->
              let (_loc_p,p) = p in
              fun f  ->
                let p =
                  match p with
                  | None  -> loc_pat _loc_p Ppat_any
                  | Some p -> p in
                { pcstr_pat = p; pcstr_fields = f }))
    let class_binding = Decap.declare_grammar "class_binding"
    let _ =
      Decap.set_grammar class_binding
        (Decap.fsequence_position virtual_flag
           (Decap.fsequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x))
                 (Decap.option []
                    (Decap.fsequence (Decap.string "[" "[")
                       (Decap.sequence type_parameters (Decap.string "]" "]")
                          (fun params  _  _  -> params)))))
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) class_name)
                 (Decap.fsequence
                    (Decap.apply List.rev
                       (Decap.fixpoint []
                          (Decap.apply (fun x  y  -> x :: y)
                             (parameter false))))
                    (Decap.fsequence
                       (Decap.option None
                          (Decap.apply (fun x  -> Some x)
                             (Decap.sequence (Decap.string ":" ":")
                                class_type (fun _  ct  -> ct))))
                       (Decap.sequence (Decap.char '=' '=') class_expr
                          (fun _  ce  ct  ps  cn  ->
                             let (_loc_cn,cn) = cn in
                             fun params  ->
                               let (_loc_params,params) = params in
                               fun v  __loc__start__buf  __loc__start__pos 
                                 __loc__end__buf  __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos in
                                 let ce = apply_params_cls _loc ps ce in
                                 let ce =
                                   match ct with
                                   | None  -> ce
                                   | Some ct ->
                                       loc_pcl _loc (Pcl_constraint (ce, ct)) in
                                 class_type_declaration
                                   ~attributes:(attach_attrib _loc [])
                                   _loc_params _loc (id_loc cn _loc_cn)
                                   params v ce)))))))
    let class_definition = Decap.declare_grammar "class_definition"
    let _ =
      Decap.set_grammar class_definition
        (Decap.sequence class_binding
           (Decap.apply List.rev
              (Decap.fixpoint []
                 (Decap.apply (fun x  y  -> x :: y)
                    (Decap.sequence and_kw class_binding
                       (fun _  _default_0  -> _default_0)))))
           (fun cb  cbs  -> cb :: cbs))
    let pexp_list _loc ?loc_cl  l =
      if l = []
      then loc_expr _loc (pexp_construct ((id_loc (Lident "[]") _loc), None))
      else
        (let loc_cl =
           ghost (match loc_cl with | None  -> _loc | Some pos -> pos) in
         List.fold_right
           (fun (x,pos)  acc  ->
              let _loc = ghost (merge2 pos loc_cl) in
              loc_expr _loc
                (pexp_construct
                   ((id_loc (Lident "::") (ghost _loc)),
                     (Some (loc_expr _loc (Pexp_tuple [x; acc])))))) l
           (loc_expr loc_cl
              (pexp_construct ((id_loc (Lident "[]") loc_cl), None))))
    let apply_lbl _loc (lbl,e) =
      let e =
        match e with
        | None  -> loc_expr _loc (Pexp_ident (id_loc (Lident lbl) _loc))
        | Some e -> e in
      (lbl, e)
    let rec mk_seq =
      function
      | [] -> assert false
      | e::[] -> e
      | x::l ->
          let res = mk_seq l in
          loc_expr (merge2 x.pexp_loc res.pexp_loc) (Pexp_sequence (x, res))
    let (extra_expressions_grammar,extra_expressions_grammar__set__grammar) =
      Decap.grammar_family "extra_expressions_grammar"
    let _ =
      extra_expressions_grammar__set__grammar
        (fun lvl  ->
           alternatives (List.map (fun g  -> g lvl) extra_expressions))
    let structure_item_simple = declare_grammar "structure_item_simple"
    let (prefix_expression,prefix_expression__set__grammar) =
      Decap.grammar_family "prefix_expression"
    let _ =
      prefix_expression__set__grammar
        (fun c  ->
           Decap.alternatives
             [Decap.sequence_position function_kw match_cases
                (fun _default_0  l  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   loc_expr _loc (pexp_function l));
             Decap.fsequence_position match_kw
               (Decap.fsequence expression
                  (Decap.sequence with_kw match_cases
                     (fun _default_0  l  e  _default_1  __loc__start__buf 
                        __loc__start__pos  __loc__end__buf  __loc__end__pos 
                        ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_expr _loc (Pexp_match (e, l)))));
             Decap.fsequence_position try_kw
               (Decap.fsequence expression
                  (Decap.sequence with_kw match_cases
                     (fun _default_0  l  e  _default_1  __loc__start__buf 
                        __loc__start__pos  __loc__end__buf  __loc__end__pos 
                        ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_expr _loc (Pexp_try (e, l)))));
             alternatives extra_prefix_expressions])
    let (if_expression,if_expression__set__grammar) =
      Decap.grammar_family "if_expression"
    let _ =
      if_expression__set__grammar
        (fun (alm,lvl)  ->
           Decap.alternatives
             [Decap.fsequence_position if_kw
                (Decap.fsequence expression
                   (Decap.fsequence then_kw
                      (Decap.fsequence
                         (expression_lvl (Match, (next_exp Seq)))
                         (Decap.sequence else_kw
                            (expression_lvl (alm, (next_exp Seq)))
                            (fun _default_0  e'  e  _default_1  c  _default_2
                                __loc__start__buf  __loc__start__pos 
                               __loc__end__buf  __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               loc_expr _loc
                                 (Pexp_ifthenelse (c, e, (Some e'))))))));
             Decap.fsequence_position if_kw
               (Decap.fsequence expression
                  (Decap.fsequence then_kw
                     (Decap.sequence (expression_lvl (alm, (next_exp Seq)))
                        no_else
                        (fun e  _default_0  _default_1  c  _default_2 
                           __loc__start__buf  __loc__start__pos 
                           __loc__end__buf  __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           loc_expr _loc (Pexp_ifthenelse (c, e, None))))))])
    let _ =
      set_expression_lvl
        (fun ((alm,lvl) as c)  ->
           Decap.alternatives ((extra_expressions_grammar c) ::
             (let y =
                let y =
                  let y =
                    let y =
                      let y =
                        let y =
                          let y =
                            let y =
                              let y =
                                let y =
                                  let y =
                                    let y =
                                      let y =
                                        let y =
                                          let y =
                                            let y =
                                              let y =
                                                let y =
                                                  let y =
                                                    let y =
                                                      let y =
                                                        let y =
                                                          let y =
                                                            let y =
                                                              let y =
                                                                let y =
                                                                  let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    [
                                                                    alternatives
                                                                    (List.map
                                                                    (fun lvl0
                                                                     ->
                                                                    if
                                                                    lvl =
                                                                    lvl0
                                                                    then
                                                                    Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (prefix_symbol
                                                                    lvl0))
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    lvl0)))
                                                                    (fun p 
                                                                    ->
                                                                    let 
                                                                    (_loc_p,p)
                                                                    = p in
                                                                    fun e  ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    mk_unary_opp
                                                                    p _loc_p
                                                                    e _loc_e)
                                                                    else
                                                                    Decap.fail
                                                                    "")
                                                                    prefix_prios);
                                                                    alternatives
                                                                    (List.map
                                                                    (fun lvl0
                                                                     ->
                                                                    let 
                                                                    (left,right)
                                                                    =
                                                                    if
                                                                    (assoc
                                                                    lvl0) =
                                                                    Left
                                                                    then
                                                                    (lvl0,
                                                                    (next_exp
                                                                    lvl0))
                                                                    else
                                                                    ((next_exp
                                                                    lvl0),
                                                                    lvl0) in
                                                                    if
                                                                    lvl =
                                                                    lvl0
                                                                    then
                                                                    Decap.fsequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    left))
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (infix_symbol
                                                                    lvl0))
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    right))
                                                                    (fun op 
                                                                    ->
                                                                    let 
                                                                    (_loc_op,op)
                                                                    = op in
                                                                    fun e  e'
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (if
                                                                    op = "::"
                                                                    then
                                                                    pexp_construct
                                                                    ((id_loc
                                                                    (Lident
                                                                    "::")
                                                                    _loc_op),
                                                                    (Some
                                                                    (loc_expr
                                                                    (ghost
                                                                    _loc)
                                                                    (Pexp_tuple
                                                                    [e'; e]))))
                                                                    else
                                                                    Pexp_apply
                                                                    ((loc_expr
                                                                    _loc_op
                                                                    (Pexp_ident
                                                                    (id_loc
                                                                    (Lident
                                                                    op)
                                                                    _loc_op))),
                                                                    [
                                                                    (nolabel,
                                                                    e');
                                                                    (nolabel,
                                                                    e)]))))
                                                                    else
                                                                    Decap.fail
                                                                    "")
                                                                    infix_prios)] in
                                                                    if
                                                                    lvl = App
                                                                    then
                                                                    (Decap.sequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    (next_exp
                                                                    App)))
                                                                    (Decap.apply
                                                                    List.rev
                                                                    (Decap.fixpoint1
                                                                    []
                                                                    (Decap.apply
                                                                    (fun x  y
                                                                     -> x ::
                                                                    y)
                                                                    argument)))
                                                                    (fun f  l
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (match 
                                                                    ((f.pexp_desc),
                                                                    l)
                                                                    with
                                                                    | 
                                                                    (Pexp_construct
                                                                    (c,None
                                                                    ,b),
                                                                    ("",a)::[])
                                                                    ->
                                                                    Pexp_construct
                                                                    (c,
                                                                    (Some a),
                                                                    b)
                                                                    | 
                                                                    (Pexp_variant
                                                                    (c,None ),
                                                                    ("",a)::[])
                                                                    ->
                                                                    Pexp_variant
                                                                    (c,
                                                                    (Some a))
                                                                    | 
                                                                    _ ->
                                                                    Pexp_apply
                                                                    (f, l))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl =
                                                                    Dash
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    Dash))
                                                                    (Decap.sequence
                                                                    (Decap.char
                                                                    '#' '#')
                                                                    method_name
                                                                    (fun _  f
                                                                     e' 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_send
                                                                    (e', f)))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    (lvl =
                                                                    Dot) ||
                                                                    (lvl =
                                                                    Aff)
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    Dot))
                                                                    (Decap.sequence
                                                                    (Decap.char
                                                                    '.' '.')
                                                                    (Decap.alternatives
                                                                    (let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    let y =
                                                                    [] in
                                                                    if
                                                                    lvl = Dot
                                                                    then
                                                                    (Decap.apply_position
                                                                    (fun f 
                                                                    ->
                                                                    let 
                                                                    (_loc_f,f)
                                                                    = f in
                                                                    fun
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    let f =
                                                                    id_loc f
                                                                    _loc_f in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_field
                                                                    (e', f)))
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x)) field))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Aff
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x)) field)
                                                                    (Decap.sequence
                                                                    (Decap.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _  e
                                                                     f  ->
                                                                    let 
                                                                    (_loc_f,f)
                                                                    = f in
                                                                    fun
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    let f =
                                                                    id_loc f
                                                                    _loc_f in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_setfield
                                                                    (e', f,
                                                                    e))))) ::
                                                                    y
                                                                    else y in
                                                                    if
                                                                    lvl = Dot
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.string
                                                                    "{" "{")
                                                                    (Decap.sequence
                                                                    expression
                                                                    (Decap.string
                                                                    "}" "}")
                                                                    (fun f  _
                                                                     _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    bigarray_get
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _loc)) e'
                                                                    f))) :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Aff
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.string
                                                                    "{" "{")
                                                                    (Decap.fsequence
                                                                    expression
                                                                    (Decap.fsequence
                                                                    (Decap.string
                                                                    "}" "}")
                                                                    (Decap.sequence
                                                                    (Decap.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _  e
                                                                     _  f  _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    bigarray_set
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _loc)) e'
                                                                    f e)))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Dot
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.string
                                                                    "[" "[")
                                                                    (Decap.sequence
                                                                    expression
                                                                    (Decap.string
                                                                    "]" "]")
                                                                    (fun f  _
                                                                     _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    exp_apply
                                                                    _loc
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _loc))
                                                                    "String"
                                                                    "get")
                                                                    [e'; f])))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Aff
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.string
                                                                    "[" "[")
                                                                    (Decap.fsequence
                                                                    expression
                                                                    (Decap.fsequence
                                                                    (Decap.string
                                                                    "]" "]")
                                                                    (Decap.sequence
                                                                    (Decap.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _  e
                                                                     _  f  _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    exp_apply
                                                                    _loc
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _loc))
                                                                    "String"
                                                                    "set")
                                                                    [e';
                                                                    f;
                                                                    e])))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Dot
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.string
                                                                    "(" "(")
                                                                    (Decap.sequence
                                                                    expression
                                                                    (Decap.string
                                                                    ")" ")")
                                                                    (fun f  _
                                                                     _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    exp_apply
                                                                    _loc
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _loc))
                                                                    "Array"
                                                                    "get")
                                                                    [e'; f])))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Aff
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.string
                                                                    "(" "(")
                                                                    (Decap.fsequence
                                                                    expression
                                                                    (Decap.fsequence
                                                                    (Decap.string
                                                                    ")" ")")
                                                                    (Decap.sequence
                                                                    (Decap.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _  e
                                                                     _  f  _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    fun e' 
                                                                    _loc  ->
                                                                    exp_apply
                                                                    _loc
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _loc))
                                                                    "Array"
                                                                    "set")
                                                                    [e';
                                                                    f;
                                                                    e])))))
                                                                    :: y
                                                                    else y))
                                                                    (fun _  r
                                                                     e' 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    r e' _loc)))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Seq
                                                                    then
                                                                    (Decap.fsequence
                                                                    (Decap.apply
                                                                    List.rev
                                                                    (Decap.fixpoint
                                                                    []
                                                                    (Decap.apply
                                                                    (fun x  y
                                                                     -> x ::
                                                                    y)
                                                                    (Decap.sequence
                                                                    (expression_lvl
                                                                    (LetRight,
                                                                    (next_exp
                                                                    Seq)))
                                                                    semi_col
                                                                    (fun
                                                                    _default_0
                                                                     _  ->
                                                                    _default_0)))))
                                                                    (Decap.sequence
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Seq)))
                                                                    (Decap.alternatives
                                                                    [semi_col;
                                                                    no_semi])
                                                                    (fun e' 
                                                                    _default_0
                                                                     ls  ->
                                                                    mk_seq
                                                                    (ls @
                                                                    [e']))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl =
                                                                    Tupl
                                                                    then
                                                                    (Decap.sequence_position
                                                                    (Decap.apply
                                                                    List.rev
                                                                    (Decap.fixpoint1
                                                                    []
                                                                    (Decap.apply
                                                                    (fun x  y
                                                                     -> x ::
                                                                    y)
                                                                    (Decap.sequence
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    (next_exp
                                                                    Tupl)))
                                                                    (Decap.char
                                                                    ',' ',')
                                                                    (fun
                                                                    _default_0
                                                                     _  ->
                                                                    _default_0)))))
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Tupl)))
                                                                    (fun l 
                                                                    e' 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_tuple
                                                                    (l @ [e']))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl =
                                                                    Atom
                                                                    then
                                                                    (Decap.fsequence_position
                                                                    (Decap.ignore_next_blank
                                                                    (Decap.char
                                                                    '$' '$'))
                                                                    (Decap.fsequence
                                                                    (Decap.option
                                                                    "expr"
                                                                    (Decap.sequence
                                                                    (Decap.ignore_next_blank
                                                                    (Decap.regexp
                                                                    ~name:"[a-z]+"
                                                                    "[a-z]+"
                                                                    (fun
                                                                    groupe 
                                                                    ->
                                                                    groupe 0)))
                                                                    (Decap.char
                                                                    ':' ':')
                                                                    (fun
                                                                    _default_0
                                                                     _  ->
                                                                    _default_0)))
                                                                    (Decap.sequence
                                                                    (Decap.ignore_next_blank
                                                                    expression)
                                                                    (Decap.char
                                                                    '$' '$')
                                                                    (fun e  _
                                                                     aq  _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let f =
                                                                    let open Quote in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let locate
                                                                    _loc e =
                                                                    quote_record
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    ((parsetree
                                                                    "pexp_desc"),
                                                                    e);
                                                                    ((parsetree
                                                                    "pexp_loc"),
                                                                    (quote_location_t
                                                                    e_loc
                                                                    _loc _loc))] in
                                                                    let generic_antiquote
                                                                    e =
                                                                    function
                                                                    | 
                                                                    Quote_pexp
                                                                     -> e
                                                                    | 
                                                                    _ ->
                                                                    failwith
                                                                    "Bad antiquotation..." in
                                                                    let quote_loc
                                                                    _loc e =
                                                                    quote_record
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    ((Ldot
                                                                    ((Lident
                                                                    "Asttypes"),
                                                                    "txt")),
                                                                    e);
                                                                    ((Ldot
                                                                    ((Lident
                                                                    "Asttypes"),
                                                                    "loc")),
                                                                    (quote_location_t
                                                                    e_loc
                                                                    _loc _loc))] in
                                                                    match aq
                                                                    with
                                                                    | 
                                                                    "expr" ->
                                                                    generic_antiquote
                                                                    e
                                                                    | 
                                                                    "longident"
                                                                    ->
                                                                    let e =
                                                                    quote_const
                                                                    e_loc
                                                                    _loc
                                                                    (parsetree
                                                                    "Pexp_ident")
                                                                    [
                                                                    quote_loc
                                                                    _loc e] in
                                                                    generic_antiquote
                                                                    (locate
                                                                    _loc e)
                                                                    | 
                                                                    "bool" ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_bool")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    "int" ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_int")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    "string"
                                                                    ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_string")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    "list" ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_list")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    "tuple"
                                                                    ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_tuple")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    "array"
                                                                    ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_array")
                                                                    [
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc _loc;
                                                                    e])
                                                                    | 
                                                                    _ ->
                                                                    give_up
                                                                    (Printf.sprintf
                                                                    "Invalid antiquotation %s."
                                                                    aq) in
                                                                    Quote.pexp_antiquotation
                                                                    _loc f))))
                                                                    :: y
                                                                    else y in
                                                                  if
                                                                    lvl =
                                                                    Atom
                                                                  then
                                                                    (
                                                                    Decap.sequence_position
                                                                    (Decap.ignore_next_blank
                                                                    (Decap.char
                                                                    '$' '$'))
                                                                    uident
                                                                    (fun _  c
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    match c
                                                                    with
                                                                    | 
                                                                    "FILE" ->
                                                                    exp_string
                                                                    _loc
                                                                    (start_pos
                                                                    _loc).Lexing.pos_fname
                                                                    | 
                                                                    "LINE" ->
                                                                    exp_int
                                                                    _loc
                                                                    (start_pos
                                                                    _loc).Lexing.pos_lnum
                                                                    | 
                                                                    _ ->
                                                                    (try
                                                                    let str =
                                                                    Sys.getenv
                                                                    c in
                                                                    parse_string
                                                                    ~filename:(
                                                                    "ENV:" ^
                                                                    c)
                                                                    expression
                                                                    ocaml_blank
                                                                    str
                                                                    with
                                                                    | 
                                                                    Not_found
                                                                     ->
                                                                    give_up
                                                                    ""))) ::
                                                                    y
                                                                  else y in
                                                                if lvl = Atom
                                                                then
                                                                  (Decap.sequence
                                                                    (Decap.string
                                                                    "<:" "<:")
                                                                    (Decap.alternatives
                                                                    [
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "expr"
                                                                    "expr")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    expression)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_expression
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "type"
                                                                    "type")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    typexpr)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_core_type
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "pat"
                                                                    "pat")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    pattern)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_pattern
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "struct"
                                                                    "struct")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    structure_item_simple)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_structure
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "sig"
                                                                    "sig")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    signature_item)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_signature
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "constructors"
                                                                    "constructors")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    constr_decl_list)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let quote_constructor_declaration
                                                                    e_loc
                                                                    _loc
                                                                    (s,t,t',l)
                                                                    =
                                                                    let open Quote in
                                                                    quote_tuple
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    (quote_loc
                                                                    quote_string)
                                                                    e_loc
                                                                    _loc s;
                                                                    (quote_list
                                                                    quote_core_type)
                                                                    e_loc
                                                                    _loc t;
                                                                    (quote_option
                                                                    quote_core_type)
                                                                    e_loc
                                                                    _loc t';
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc l] in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let open Quote in
                                                                    quote_list
                                                                    quote_constructor_declaration
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "fields"
                                                                    "fields")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    field_decl_list)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let quote_label_declaration
                                                                    e_loc
                                                                    _loc
                                                                    (x1,x2,x3,x4)
                                                                    =
                                                                    let open Quote in
                                                                    quote_tuple
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    quote_loc
                                                                    quote_string
                                                                    e_loc
                                                                    _loc x1;
                                                                    quote_mutable_flag
                                                                    e_loc
                                                                    _loc x2;
                                                                    quote_core_type
                                                                    e_loc
                                                                    _loc x3;
                                                                    quote_location_t
                                                                    e_loc
                                                                    _loc x4] in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let open Quote in
                                                                    quote_list
                                                                    quote_label_declaration
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "bindings"
                                                                    "bindings")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    let_binding)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let quote_value_binding
                                                                    e_loc
                                                                    _loc
                                                                    (x1,x2) =
                                                                    let open Quote in
                                                                    quote_tuple
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    quote_pattern
                                                                    e_loc
                                                                    _loc x1;
                                                                    quote_expression
                                                                    e_loc
                                                                    _loc x2] in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let open Quote in
                                                                    quote_list
                                                                    quote_value_binding
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "cases"
                                                                    "cases")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    match_cases)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let quote_case
                                                                    e_loc
                                                                    _loc
                                                                    (x1,x2) =
                                                                    let open Quote in
                                                                    quote_tuple
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    quote_pattern
                                                                    e_loc
                                                                    _loc x1;
                                                                    quote_expression
                                                                    e_loc
                                                                    _loc x2] in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let open Quote in
                                                                    quote_list
                                                                    quote_case
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "module"
                                                                    "module")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_expr)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_module_expr
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "module"
                                                                    "module")
                                                                    (Decap.fsequence
                                                                    (Decap.string
                                                                    "type"
                                                                    "type")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_type)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _  _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_module_type
                                                                    e_loc
                                                                    _loc_e e))));
                                                                    Decap.fsequence_position
                                                                    (Decap.string
                                                                    "record"
                                                                    "record")
                                                                    (Decap.fsequence
                                                                    (Decap.char
                                                                    '<' '<')
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    record_list)
                                                                    (Decap.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    let quote_fields
                                                                    =
                                                                    let open Quote in
                                                                    quote_list
                                                                    (fun
                                                                    e_loc 
                                                                    _loc 
                                                                    (x1,x2) 
                                                                    ->
                                                                    quote_tuple
                                                                    e_loc
                                                                    _loc
                                                                    [
                                                                    (quote_loc
                                                                    quote_longident)
                                                                    e_loc
                                                                    _loc x1;
                                                                    quote_expression
                                                                    e_loc
                                                                    _loc x2]) in
                                                                    quote_fields
                                                                    e_loc
                                                                    _loc_e e)))])
                                                                    (fun _  r
                                                                     -> r))
                                                                  :: y
                                                                else y in
                                                              if lvl = Atom
                                                              then
                                                                (Decap.fsequence_position
                                                                   (Decap.string
                                                                    "(" "(")
                                                                   (Decap.fsequence
                                                                    module_kw
                                                                    (Decap.fsequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_expr)
                                                                    (Decap.sequence
                                                                    (Decap.apply_position
                                                                    (fun x 
                                                                    str  pos 
                                                                    str' 
                                                                    pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (Decap.option
                                                                    None
                                                                    (Decap.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Decap.sequence
                                                                    (Decap.string
                                                                    ":" ":")
                                                                    package_type
                                                                    (fun _ 
                                                                    pt  -> pt)))))
                                                                    (Decap.string
                                                                    ")" ")")
                                                                    (fun pt 
                                                                    ->
                                                                    let 
                                                                    (_loc_pt,pt)
                                                                    = pt in
                                                                    fun _  me
                                                                     ->
                                                                    let 
                                                                    (_loc_me,me)
                                                                    = me in
                                                                    fun
                                                                    _default_0
                                                                     _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let desc
                                                                    =
                                                                    match pt
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    Pexp_pack
                                                                    me
                                                                    | 
                                                                    Some pt
                                                                    ->
                                                                    let me =
                                                                    loc_expr
                                                                    _loc_me
                                                                    (Pexp_pack
                                                                    me) in
                                                                    let pt =
                                                                    loc_typ
                                                                    _loc_pt
                                                                    pt in
                                                                    pexp_constraint
                                                                    (me, pt) in
                                                                    loc_expr
                                                                    _loc desc)))))
                                                                :: y
                                                              else y in
                                                            if lvl = Atom
                                                            then
                                                              (Decap.fsequence_position
                                                                 (Decap.string
                                                                    "{<" "{<")
                                                                 (Decap.sequence
                                                                    (
                                                                    Decap.option
                                                                    []
                                                                    (Decap.fsequence
                                                                    obj_item
                                                                    (Decap.sequence
                                                                    (Decap.apply
                                                                    List.rev
                                                                    (Decap.fixpoint
                                                                    []
                                                                    (Decap.apply
                                                                    (fun x  y
                                                                     -> x ::
                                                                    y)
                                                                    (Decap.sequence
                                                                    semi_col
                                                                    obj_item
                                                                    (fun _  o
                                                                     -> o)))))
                                                                    (Decap.option
                                                                    None
                                                                    (Decap.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    semi_col))
                                                                    (fun l  _
                                                                     o  -> o
                                                                    :: l))))
                                                                    (
                                                                    Decap.string
                                                                    ">}" ">}")
                                                                    (
                                                                    fun l  _ 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_override
                                                                    l))))
                                                              :: y
                                                            else y in
                                                          if lvl = Atom
                                                          then
                                                            (Decap.fsequence_position
                                                               object_kw
                                                               (Decap.sequence
                                                                  class_body
                                                                  end_kw
                                                                  (fun o 
                                                                    _default_0
                                                                     _default_1
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_object
                                                                    o))))
                                                            :: y
                                                          else y in
                                                        if lvl = Atom
                                                        then
                                                          (Decap.sequence_position
                                                             new_kw
                                                             (Decap.apply_position
                                                                (fun x  str 
                                                                   pos  str' 
                                                                   pos'  ->
                                                                   ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                class_path)
                                                             (fun _default_0 
                                                                p  ->
                                                                let (_loc_p,p)
                                                                  = p in
                                                                fun
                                                                  __loc__start__buf
                                                                   __loc__start__pos
                                                                   __loc__end__buf
                                                                   __loc__end__pos
                                                                   ->
                                                                  let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                  loc_expr
                                                                    _loc
                                                                    (
                                                                    Pexp_new
                                                                    (id_loc p
                                                                    _loc_p))))
                                                          :: y
                                                        else y in
                                                      if lvl = Atom
                                                      then
                                                        (Decap.fsequence_position
                                                           for_kw
                                                           (Decap.fsequence
                                                              (Decap.apply_position
                                                                 (fun x  str 
                                                                    pos  str'
                                                                     pos'  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                 lident)
                                                              (Decap.fsequence
                                                                 (Decap.char
                                                                    '=' '=')
                                                                 (Decap.fsequence
                                                                    expression
                                                                    (
                                                                    Decap.fsequence
                                                                    downto_flag
                                                                    (Decap.fsequence
                                                                    expression
                                                                    (Decap.fsequence
                                                                    do_kw
                                                                    (Decap.sequence
                                                                    expression
                                                                    done_kw
                                                                    (fun e'' 
                                                                    _default_0
                                                                     _default_1
                                                                     e'  d  e
                                                                     _  id 
                                                                    ->
                                                                    let 
                                                                    (_loc_id,id)
                                                                    = id in
                                                                    fun
                                                                    _default_2
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_for
                                                                    ((id_loc
                                                                    id
                                                                    _loc_id),
                                                                    e, e', d,
                                                                    e'')))))))))))
                                                        :: y
                                                      else y in
                                                    if lvl = Atom
                                                    then
                                                      (Decap.fsequence_position
                                                         while_kw
                                                         (Decap.fsequence
                                                            expression
                                                            (Decap.fsequence
                                                               do_kw
                                                               (Decap.sequence
                                                                  expression
                                                                  done_kw
                                                                  (fun e' 
                                                                    _default_0
                                                                     _default_1
                                                                     e 
                                                                    _default_2
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_while
                                                                    (e, e')))))))
                                                      :: y
                                                    else y in
                                                  if lvl = Atom
                                                  then
                                                    (Decap.fsequence_position
                                                       (Decap.string "{" "{")
                                                       (Decap.fsequence
                                                          (Decap.option None
                                                             (Decap.apply
                                                                (fun x  ->
                                                                   Some x)
                                                                (Decap.sequence
                                                                   expression
                                                                   with_kw
                                                                   (fun
                                                                    _default_0
                                                                     _  ->
                                                                    _default_0))))
                                                          (Decap.sequence
                                                             record_list
                                                             (Decap.string
                                                                "}" "}")
                                                             (fun l  _  e  _ 
                                                                __loc__start__buf
                                                                 __loc__start__pos
                                                                 __loc__end__buf
                                                                 __loc__end__pos
                                                                 ->
                                                                let _loc =
                                                                  locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                loc_expr _loc
                                                                  (Pexp_record
                                                                    (l, e))))))
                                                    :: y
                                                  else y in
                                                if lvl = Atom
                                                then
                                                  (Decap.fsequence_position
                                                     (Decap.char '[' '[')
                                                     (Decap.sequence
                                                        expression_list
                                                        (Decap.apply_position
                                                           (fun x  str  pos 
                                                              str'  pos'  ->
                                                              ((locate str
                                                                  pos str'
                                                                  pos'), x))
                                                           (Decap.char ']'
                                                              ']'))
                                                        (fun l  cl  ->
                                                           let (_loc_cl,cl) =
                                                             cl in
                                                           fun _ 
                                                             __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos
                                                              ->
                                                             let _loc =
                                                               locate
                                                                 __loc__start__buf
                                                                 __loc__start__pos
                                                                 __loc__end__buf
                                                                 __loc__end__pos in
                                                             loc_expr _loc
                                                               (pexp_list
                                                                  _loc
                                                                  ~loc_cl:_loc_cl
                                                                  l).pexp_desc)))
                                                  :: y
                                                else y in
                                              if lvl = Atom
                                              then
                                                (Decap.fsequence_position
                                                   (Decap.string "[|" "[|")
                                                   (Decap.sequence
                                                      expression_list
                                                      (Decap.string "|]" "|]")
                                                      (fun l  _  _ 
                                                         __loc__start__buf 
                                                         __loc__start__pos 
                                                         __loc__end__buf 
                                                         __loc__end__pos  ->
                                                         let _loc =
                                                           locate
                                                             __loc__start__buf
                                                             __loc__start__pos
                                                             __loc__end__buf
                                                             __loc__end__pos in
                                                         loc_expr _loc
                                                           (Pexp_array
                                                              (List.map fst l)))))
                                                :: y
                                              else y in
                                            if lvl = Atom
                                            then
                                              (Decap.apply_position
                                                 (fun l  __loc__start__buf 
                                                    __loc__start__pos 
                                                    __loc__end__buf 
                                                    __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    loc_expr _loc
                                                      (Pexp_variant (l, None)))
                                                 tag_name)
                                              :: y
                                            else y in
                                          if lvl = Atom
                                          then
                                            (Decap.sequence_position
                                               (Decap.apply_position
                                                  (fun x  str  pos  str' 
                                                     pos'  ->
                                                     ((locate str pos str'
                                                         pos'), x))
                                                  constructor) no_dot
                                               (fun c  ->
                                                  let (_loc_c,c) = c in
                                                  fun _default_0 
                                                    __loc__start__buf 
                                                    __loc__start__pos 
                                                    __loc__end__buf 
                                                    __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    loc_expr _loc
                                                      (pexp_construct
                                                         ((id_loc c _loc_c),
                                                           None))))
                                            :: y
                                          else y in
                                        if lvl = App
                                        then
                                          (Decap.sequence_position lazy_kw
                                             (expression_lvl
                                                (NoMatch, (next_exp App)))
                                             (fun _default_0  e 
                                                __loc__start__buf 
                                                __loc__start__pos 
                                                __loc__end__buf 
                                                __loc__end__pos  ->
                                                let _loc =
                                                  locate __loc__start__buf
                                                    __loc__start__pos
                                                    __loc__end__buf
                                                    __loc__end__pos in
                                                loc_expr _loc (Pexp_lazy e)))
                                          :: y
                                        else y in
                                      if lvl = App
                                      then
                                        (Decap.sequence_position assert_kw
                                           (Decap.alternatives
                                              ((Decap.apply_position
                                                  (fun _default_0 
                                                     __loc__start__buf 
                                                     __loc__start__pos 
                                                     __loc__end__buf 
                                                     __loc__end__pos  ->
                                                     let _loc =
                                                       locate
                                                         __loc__start__buf
                                                         __loc__start__pos
                                                         __loc__end__buf
                                                         __loc__end__pos in
                                                     pexp_assertfalse _loc)
                                                  false_kw) ::
                                              (let y = [] in
                                               if lvl = App
                                               then
                                                 (Decap.sequence no_false
                                                    (expression_lvl
                                                       (NoMatch,
                                                         (next_exp App)))
                                                    (fun _  e  ->
                                                       Pexp_assert e))
                                                 :: y
                                               else y)))
                                           (fun _default_0  e 
                                              __loc__start__buf 
                                              __loc__start__pos 
                                              __loc__end__buf 
                                              __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              loc_expr _loc e))
                                        :: y
                                      else y in
                                    if lvl = Atom
                                    then
                                      (Decap.fsequence_position begin_kw
                                         (Decap.sequence
                                            (Decap.option None
                                               (Decap.apply
                                                  (fun x  -> Some x)
                                                  expression)) end_kw
                                            (fun e  _default_0  _default_1 
                                               __loc__start__buf 
                                               __loc__start__pos 
                                               __loc__end__buf 
                                               __loc__end__pos  ->
                                               let _loc =
                                                 locate __loc__start__buf
                                                   __loc__start__pos
                                                   __loc__end__buf
                                                   __loc__end__pos in
                                               match e with
                                               | Some e -> e
                                               | None  ->
                                                   let cunit =
                                                     id_loc (Lident "()")
                                                       _loc in
                                                   loc_expr _loc
                                                     (pexp_construct
                                                        (cunit, None)))))
                                      :: y
                                    else y in
                                  if lvl = Atom
                                  then
                                    (Decap.fsequence_position
                                       (Decap.char '(' '(')
                                       (Decap.fsequence no_parser
                                          (Decap.fsequence expression
                                             (Decap.sequence type_coercion
                                                (Decap.char ')' ')')
                                                (fun t  _  e  _default_0  _ 
                                                   __loc__start__buf 
                                                   __loc__start__pos 
                                                   __loc__end__buf 
                                                   __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   match t with
                                                   | (Some t1,None ) ->
                                                       loc_expr _loc
                                                         (pexp_constraint
                                                            (e, t1))
                                                   | (t1,Some t2) ->
                                                       loc_expr _loc
                                                         (pexp_coerce
                                                            (e, t1, t2))
                                                   | (None ,None ) ->
                                                       assert false)))))
                                    :: y
                                  else y in
                                if lvl = Atom
                                then
                                  (Decap.fsequence_position
                                     (Decap.char '(' '(')
                                     (Decap.sequence
                                        (Decap.option None
                                           (Decap.apply (fun x  -> Some x)
                                              expression))
                                        (Decap.char ')' ')')
                                        (fun e  _  _  __loc__start__buf 
                                           __loc__start__pos  __loc__end__buf
                                            __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           match e with
                                           | Some e ->
                                               if
                                                 e.pexp_desc ==
                                                   Quote.dummy_pexp
                                               then e
                                               else loc_expr _loc e.pexp_desc
                                           | None  ->
                                               let cunit =
                                                 id_loc (Lident "()") _loc in
                                               loc_expr _loc
                                                 (pexp_construct
                                                    (cunit, None)))))
                                  :: y
                                else y in
                              if (allow_let alm) && (lvl < App)
                              then
                                (Decap.sequence_position let_kw
                                   (Decap.alternatives
                                      (let y =
                                         [Decap.fsequence_position module_kw
                                            (Decap.fsequence module_name
                                               (Decap.fsequence
                                                  (Decap.apply List.rev
                                                     (Decap.fixpoint []
                                                        (Decap.apply
                                                           (fun x  y  -> x ::
                                                              y)
                                                           (Decap.fsequence_position
                                                              (Decap.char '('
                                                                 '(')
                                                              (Decap.fsequence
                                                                 module_name
                                                                 (Decap.fsequence
                                                                    (
                                                                    Decap.char
                                                                    ':' ':')
                                                                    (
                                                                    Decap.sequence
                                                                    module_type
                                                                    (Decap.char
                                                                    ')' ')')
                                                                    (fun mt 
                                                                    _  _  mn 
                                                                    _ 
                                                                    __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    (mn, mt,
                                                                    _loc)))))))))
                                                  (Decap.fsequence
                                                     (Decap.apply_position
                                                        (fun x  str  pos 
                                                           str'  pos'  ->
                                                           ((locate str pos
                                                               str' pos'), x))
                                                        (Decap.option None
                                                           (Decap.apply
                                                              (fun x  ->
                                                                 Some x)
                                                              (Decap.sequence
                                                                 (Decap.string
                                                                    ":" ":")
                                                                 module_type
                                                                 (fun _  mt 
                                                                    -> mt)))))
                                                     (Decap.fsequence
                                                        (Decap.string "=" "=")
                                                        (Decap.fsequence
                                                           (Decap.apply_position
                                                              (fun x  str 
                                                                 pos  str' 
                                                                 pos'  ->
                                                                 ((locate str
                                                                    pos str'
                                                                    pos'), x))
                                                              module_expr)
                                                           (Decap.sequence
                                                              in_kw
                                                              (expression_lvl
                                                                 ((right_alm
                                                                    alm),
                                                                   Seq))
                                                              (fun _default_0
                                                                  e  me  ->
                                                                 let 
                                                                   (_loc_me,me)
                                                                   = me in
                                                                 fun _  mt 
                                                                   ->
                                                                   let 
                                                                    (_loc_mt,mt)
                                                                    = mt in
                                                                   fun l  mn 
                                                                    _default_1
                                                                     __loc__start__buf
                                                                     __loc__start__pos
                                                                     __loc__end__buf
                                                                     __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let me =
                                                                    match mt
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    me
                                                                    | 
                                                                    Some mt
                                                                    ->
                                                                    mexpr_loc
                                                                    (merge2
                                                                    _loc_mt
                                                                    _loc_me)
                                                                    (Pmod_constraint
                                                                    (me, mt)) in
                                                                    let me =
                                                                    List.fold_left
                                                                    (fun acc 
                                                                    (mn,mt,_loc)
                                                                     ->
                                                                    mexpr_loc
                                                                    (merge2
                                                                    _loc
                                                                    _loc_me)
                                                                    (Pmod_functor
                                                                    (mn, mt,
                                                                    acc))) me
                                                                    (List.rev
                                                                    l) in
                                                                    fun _loc 
                                                                    ->
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_letmodule
                                                                    (mn, me,
                                                                    e)))))))));
                                         Decap.fsequence_position open_kw
                                           (Decap.fsequence override_flag
                                              (Decap.fsequence
                                                 (Decap.apply_position
                                                    (fun x  str  pos  str' 
                                                       pos'  ->
                                                       ((locate str pos str'
                                                           pos'), x))
                                                    module_path)
                                                 (Decap.sequence in_kw
                                                    (expression_lvl
                                                       ((right_alm alm), Seq))
                                                    (fun _default_0  e  mp 
                                                       ->
                                                       let (_loc_mp,mp) = mp in
                                                       fun o  _default_1 
                                                         __loc__start__buf 
                                                         __loc__start__pos 
                                                         __loc__end__buf 
                                                         __loc__end__pos  ->
                                                         let _loc =
                                                           locate
                                                             __loc__start__buf
                                                             __loc__start__pos
                                                             __loc__end__buf
                                                             __loc__end__pos in
                                                         let mp =
                                                           id_loc mp _loc_mp in
                                                         fun _loc  ->
                                                           loc_expr _loc
                                                             (Pexp_open
                                                                (o, mp, e))))))] in
                                       if (allow_let alm) && (lvl < App)
                                       then
                                         (Decap.fsequence_position rec_flag
                                            (Decap.fsequence let_binding
                                               (Decap.fsequence in_kw
                                                  (Decap.sequence
                                                     (expression_lvl
                                                        ((right_alm alm),
                                                          Seq)) no_semi
                                                     (fun e  _default_0 
                                                        _default_1  l  r 
                                                        __loc__start__buf 
                                                        __loc__start__pos 
                                                        __loc__end__buf 
                                                        __loc__end__pos  ->
                                                        let _loc =
                                                          locate
                                                            __loc__start__buf
                                                            __loc__start__pos
                                                            __loc__end__buf
                                                            __loc__end__pos in
                                                        fun _loc  ->
                                                          loc_expr _loc
                                                            (Pexp_let
                                                               (r, l, e)))))))
                                         :: y
                                       else y))
                                   (fun _default_0  r  __loc__start__buf 
                                      __loc__start__pos  __loc__end__buf 
                                      __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos in
                                      r _loc))
                                :: y
                              else y in
                            if (allow_let alm) && (lvl < App)
                            then
                              (Decap.fsequence_position fun_kw
                                 (Decap.fsequence
                                    (Decap.apply List.rev
                                       (Decap.fixpoint []
                                          (Decap.apply (fun x  y  -> x :: y)
                                             (Decap.apply
                                                (fun lbl  ->
                                                   let (_loc_lbl,lbl) = lbl in
                                                   (lbl, _loc_lbl))
                                                (Decap.apply_position
                                                   (fun x  str  pos  str' 
                                                      pos'  ->
                                                      ((locate str pos str'
                                                          pos'), x))
                                                   (parameter true))))))
                                    (Decap.fsequence arrow_re
                                       (Decap.sequence
                                          (expression_lvl
                                             ((right_alm alm), Seq)) no_semi
                                          (fun e  _default_0  _default_1  l 
                                             _default_2  __loc__start__buf 
                                             __loc__start__pos 
                                             __loc__end__buf  __loc__end__pos
                                              ->
                                             let _loc =
                                               locate __loc__start__buf
                                                 __loc__start__pos
                                                 __loc__end__buf
                                                 __loc__end__pos in
                                             loc_expr _loc
                                               (apply_params l e).pexp_desc)))))
                              :: y
                            else y in
                          if
                            ((allow_let alm) && (lvl < App)) ||
                              ((lvl = If) && (alm <> MatchRight))
                          then (if_expression c) :: y
                          else y in
                        if (allow_match alm) && (lvl < App)
                        then (prefix_expression c) :: y
                        else y in
                      if lvl = Atom
                      then
                        (Decap.fsequence_position
                           (Decap.apply_position
                              (fun x  str  pos  str'  pos'  ->
                                 ((locate str pos str' pos'), x)) module_path)
                           (Decap.fsequence (Decap.string "." ".")
                              (Decap.fsequence (Decap.string "(" "(")
                                 (Decap.sequence expression
                                    (Decap.string ")" ")")
                                    (fun e  _  _  _  mp  ->
                                       let (_loc_mp,mp) = mp in
                                       fun __loc__start__buf 
                                         __loc__start__pos  __loc__end__buf 
                                         __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         let mp = id_loc mp _loc_mp in
                                         loc_expr _loc
                                           (Pexp_open (Fresh, mp, e)))))))
                        :: y
                      else y in
                    if lvl = Atom
                    then
                      (Decap.apply_position
                         (fun c  __loc__start__buf  __loc__start__pos 
                            __loc__end__buf  __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            loc_expr _loc (Pexp_constant c)) constant)
                      :: y
                    else y in
                  if lvl = Atom
                  then
                    (Decap.apply_position
                       (fun id  ->
                          let (_loc_id,id) = id in
                          fun __loc__start__buf  __loc__start__pos 
                            __loc__end__buf  __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            loc_expr _loc (Pexp_ident (id_loc id _loc_id)))
                       (Decap.apply_position
                          (fun x  str  pos  str'  pos'  ->
                             ((locate str pos str' pos'), x)) value_path))
                    :: y
                  else y in
                if lvl = Aff
                then
                  (Decap.fsequence_position
                     (Decap.apply_position
                        (fun x  str  pos  str'  pos'  ->
                           ((locate str pos str' pos'), x)) inst_var_name)
                     (Decap.sequence (Decap.string "<-" "<-")
                        (expression_lvl ((right_alm alm), (next_exp Aff)))
                        (fun _  e  v  ->
                           let (_loc_v,v) = v in
                           fun __loc__start__buf  __loc__start__pos 
                             __loc__end__buf  __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos in
                             loc_expr _loc
                               (Pexp_setinstvar ((id_loc v _loc_v), e)))))
                  :: y
                else y in
              if (lvl < Atom) && (lvl != Seq)
              then (expression_lvl ((left_alm alm), (next_exp lvl))) :: y
              else y)))
    let module_expr_base = Decap.declare_grammar "module_expr_base"
    let _ =
      Decap.set_grammar module_expr_base
        (Decap.alternatives
           [Decap.apply_position
              (fun mp  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                 __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 let mid = id_loc mp _loc in mexpr_loc _loc (Pmod_ident mid))
              module_path;
           Decap.fsequence_position struct_kw
             (Decap.sequence structure end_kw
                (fun ms  _default_0  _default_1  __loc__start__buf 
                   __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   mexpr_loc _loc (Pmod_structure ms)));
           Decap.fsequence_position functor_kw
             (Decap.fsequence (Decap.char '(' '(')
                (Decap.fsequence module_name
                   (Decap.fsequence (Decap.char ':' ':')
                      (Decap.fsequence module_type
                         (Decap.fsequence (Decap.char ')' ')')
                            (Decap.sequence arrow_re module_expr
                               (fun _default_0  me  _  mt  _  mn  _ 
                                  _default_1  __loc__start__buf 
                                  __loc__start__pos  __loc__end__buf 
                                  __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  mexpr_loc _loc (Pmod_functor (mn, mt, me)))))))));
           Decap.fsequence_position (Decap.char '(' '(')
             (Decap.fsequence module_expr
                (Decap.sequence
                   (Decap.option None
                      (Decap.apply (fun x  -> Some x)
                         (Decap.sequence (Decap.char ':' ':') module_type
                            (fun _  mt  -> mt)))) (Decap.char ')' ')')
                   (fun mt  _  me  _  __loc__start__buf  __loc__start__pos 
                      __loc__end__buf  __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      match mt with
                      | None  -> me
                      | Some mt -> mexpr_loc _loc (Pmod_constraint (me, mt)))));
           Decap.fsequence_position (Decap.char '(' '(')
             (Decap.fsequence val_kw
                (Decap.fsequence expression
                   (Decap.sequence
                      (Decap.apply_position
                         (fun x  str  pos  str'  pos'  ->
                            ((locate str pos str' pos'), x))
                         (Decap.option None
                            (Decap.apply (fun x  -> Some x)
                               (Decap.sequence (Decap.string ":" ":")
                                  package_type (fun _  pt  -> pt)))))
                      (Decap.char ')' ')')
                      (fun pt  ->
                         let (_loc_pt,pt) = pt in
                         fun _  e  _default_0  _  __loc__start__buf 
                           __loc__start__pos  __loc__end__buf 
                           __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           let e =
                             match pt with
                             | None  -> Pmod_unpack e
                             | Some pt ->
                                 let pt = loc_typ _loc_pt pt in
                                 Pmod_unpack
                                   (loc_expr _loc (pexp_constraint (e, pt))) in
                           mexpr_loc _loc e))))])
    let _ =
      set_grammar module_expr
        (Decap.sequence
           (Decap.apply_position
              (fun x  str  pos  str'  pos'  ->
                 ((locate str pos str' pos'), x)) module_expr_base)
           (Decap.apply List.rev
              (Decap.fixpoint []
                 (Decap.apply (fun x  y  -> x :: y)
                    (Decap.fsequence_position (Decap.string "(" "(")
                       (Decap.sequence module_expr (Decap.string ")" ")")
                          (fun m  _  _  __loc__start__buf  __loc__start__pos 
                             __loc__end__buf  __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos in
                             (_loc, m)))))))
           (fun m  ->
              let (_loc_m,m) = m in
              fun l  ->
                List.fold_left
                  (fun acc  (_loc_n,n)  ->
                     mexpr_loc (merge2 _loc_m _loc_n) (Pmod_apply (acc, n)))
                  m l))
    let module_type_base = Decap.declare_grammar "module_type_base"
    let _ =
      Decap.set_grammar module_type_base
        (Decap.alternatives
           [Decap.apply_position
              (fun mp  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                 __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 let mid = id_loc mp _loc in mtyp_loc _loc (Pmty_ident mid))
              modtype_path;
           Decap.fsequence_position sig_kw
             (Decap.sequence signature end_kw
                (fun ms  _default_0  _default_1  __loc__start__buf 
                   __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   mtyp_loc _loc (Pmty_signature ms)));
           Decap.fsequence_position functor_kw
             (Decap.fsequence (Decap.char '(' '(')
                (Decap.fsequence module_name
                   (Decap.fsequence (Decap.char ':' ':')
                      (Decap.fsequence module_type
                         (Decap.fsequence (Decap.char ')' ')')
                            (Decap.fsequence arrow_re
                               (Decap.sequence module_type no_with
                                  (fun me  _default_0  _default_1  _  mt  _ 
                                     mn  _  _default_2  __loc__start__buf 
                                     __loc__start__pos  __loc__end__buf 
                                     __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     mtyp_loc _loc
                                       (Pmty_functor (mn, mt, me))))))))));
           Decap.fsequence (Decap.string "(" "(")
             (Decap.sequence module_type (Decap.string ")" ")")
                (fun mt  _  _  -> mt));
           Decap.fsequence_position module_kw
             (Decap.fsequence type_kw
                (Decap.sequence of_kw module_expr
                   (fun _default_0  me  _default_1  _default_2 
                      __loc__start__buf  __loc__start__pos  __loc__end__buf 
                      __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      mtyp_loc _loc (Pmty_typeof me))))])
    let mod_constraint = Decap.declare_grammar "mod_constraint"
    let _ =
      Decap.set_grammar mod_constraint
        (Decap.alternatives
           [Decap.sequence
              (Decap.apply_position
                 (fun x  str  pos  str'  pos'  ->
                    ((locate str pos str' pos'), x)) type_kw)
              typedef_in_constraint
              (fun t  ->
                 let (_loc_t,t) = t in
                 fun tf  ->
                   let (tn,ty) = tf (Some _loc_t) in (tn, (Pwith_type ty)));
           Decap.fsequence module_kw
             (Decap.fsequence
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x)) module_path)
                (Decap.sequence (Decap.char '=' '=')
                   (Decap.apply_position
                      (fun x  str  pos  str'  pos'  ->
                         ((locate str pos str' pos'), x))
                      extended_module_path)
                   (fun _  m2  ->
                      let (_loc_m2,m2) = m2 in
                      fun m1  ->
                        let (_loc_m1,m1) = m1 in
                        fun _default_0  ->
                          let name = id_loc m1 _loc_m1 in
                          (name, (Pwith_module (id_loc m2 _loc_m2))))));
           Decap.fsequence_position type_kw
             (Decap.fsequence (Decap.option [] type_params)
                (Decap.fsequence
                   (Decap.apply_position
                      (fun x  str  pos  str'  pos'  ->
                         ((locate str pos str' pos'), x)) typeconstr_name)
                   (Decap.sequence (Decap.string ":=" ":=") typexpr
                      (fun _  te  tcn  ->
                         let (_loc_tcn,tcn) = tcn in
                         fun tps  _default_0  __loc__start__buf 
                           __loc__start__pos  __loc__end__buf 
                           __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           let td =
                             type_declaration _loc (id_loc tcn _loc_tcn) tps
                               [] Ptype_abstract Public (Some te) in
                           ((id_loc (Lident tcn) _loc_tcn),
                             (Pwith_typesubst td))))));
           Decap.fsequence module_kw
             (Decap.fsequence module_name
                (Decap.sequence (Decap.string ":=" ":=")
                   (Decap.apply_position
                      (fun x  str  pos  str'  pos'  ->
                         ((locate str pos str' pos'), x))
                      extended_module_path)
                   (fun _  emp  ->
                      let (_loc_emp,emp) = emp in
                      fun mn  _default_0  ->
                        ({ txt = (Lident (mn.txt)); loc = (mn.loc) },
                          (Pwith_modsubst (id_loc emp _loc_emp))))))])
    let _ =
      set_grammar module_type
        (Decap.sequence_position module_type_base
           (Decap.option None
              (Decap.apply (fun x  -> Some x)
                 (Decap.fsequence with_kw
                    (Decap.sequence mod_constraint
                       (Decap.apply List.rev
                          (Decap.fixpoint []
                             (Decap.apply (fun x  y  -> x :: y)
                                (Decap.sequence and_kw mod_constraint
                                   (fun _  _default_0  -> _default_0)))))
                       (fun m  l  _  -> m :: l)))))
           (fun m  l  __loc__start__buf  __loc__start__pos  __loc__end__buf 
              __loc__end__pos  ->
              let _loc =
                locate __loc__start__buf __loc__start__pos __loc__end__buf
                  __loc__end__pos in
              match l with
              | None  -> m
              | Some l -> mtyp_loc _loc (Pmty_with (m, l))))
    let structure_item_base = Decap.declare_grammar "structure_item_base"
    let _ =
      Decap.set_grammar structure_item_base
        (Decap.alternatives
           [Decap.fsequence_position
              (Decap.regexp ~name:"let" let_re (fun groupe  -> groupe 0))
              (Decap.sequence rec_flag let_binding
                 (fun r  l  _default_0  __loc__start__buf  __loc__start__pos 
                    __loc__end__buf  __loc__end__pos  ->
                    let _loc =
                      locate __loc__start__buf __loc__start__pos
                        __loc__end__buf __loc__end__pos in
                    loc_str _loc
                      (match l with
                       | ({ ppat_desc = Ppat_any ; ppat_loc = _ },e)::[] ->
                           pstr_eval e
                       | _ -> Pstr_value (r, l))));
           Decap.fsequence_position external_kw
             (Decap.fsequence
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x)) value_name)
                (Decap.fsequence (Decap.string ":" ":")
                   (Decap.fsequence typexpr
                      (Decap.fsequence (Decap.string "=" "=")
                         (Decap.sequence
                            (Decap.apply List.rev
                               (Decap.fixpoint []
                                  (Decap.apply (fun x  y  -> x :: y)
                                     string_litteral))) post_item_attributes
                            (fun ls  a  _  ty  _  n  ->
                               let (_loc_n,n) = n in
                               fun _default_0  __loc__start__buf 
                                 __loc__start__pos  __loc__end__buf 
                                 __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos in
                                 let l = List.length ls in
                                 if (l < 1) || (l > 3) then give_up "";
                                 loc_str _loc
                                   (Pstr_primitive
                                      ((id_loc n _loc_n),
                                        {
                                          pval_type = ty;
                                          pval_prim = ls;
                                          pval_loc = _loc
                                        }))))))));
           Decap.apply_position
             (fun td  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_str _loc (Pstr_type td)) type_definition;
           Decap.apply_position
             (fun ex  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_str _loc ex) exception_definition;
           Decap.sequence module_kw
             (Decap.alternatives
                [Decap.fsequence_position rec_kw
                   (Decap.fsequence module_name
                      (Decap.fsequence (Decap.string ":" ":")
                         (Decap.fsequence module_type
                            (Decap.fsequence (Decap.char '=' '=')
                               (Decap.sequence module_expr
                                  (Decap.apply List.rev
                                     (Decap.fixpoint []
                                        (Decap.apply (fun x  y  -> x :: y)
                                           (Decap.fsequence_position and_kw
                                              (Decap.fsequence module_name
                                                 (Decap.fsequence
                                                    (Decap.string ":" ":")
                                                    (Decap.fsequence
                                                       module_type
                                                       (Decap.sequence
                                                          (Decap.char '=' '=')
                                                          module_expr
                                                          (fun _  me  mt  _ 
                                                             mn  _default_0 
                                                             __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos
                                                              ->
                                                             let _loc =
                                                               locate
                                                                 __loc__start__buf
                                                                 __loc__start__pos
                                                                 __loc__end__buf
                                                                 __loc__end__pos in
                                                             module_binding
                                                               _loc mn mt me)))))))))
                                  (fun me  ms  _  mt  _  mn  _default_0 
                                     __loc__start__buf  __loc__start__pos 
                                     __loc__end__buf  __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     let m = module_binding _loc mn mt me in
                                     loc_str _loc (Pstr_recmodule (m :: ms))))))));
                Decap.fsequence_position module_name
                  (Decap.fsequence
                     (Decap.apply List.rev
                        (Decap.fixpoint []
                           (Decap.apply (fun x  y  -> x :: y)
                              (Decap.fsequence_position
                                 (Decap.string "(" "(")
                                 (Decap.fsequence module_name
                                    (Decap.fsequence (Decap.string ":" ":")
                                       (Decap.sequence module_type
                                          (Decap.string ")" ")")
                                          (fun mt  _  _  mn  _ 
                                             __loc__start__buf 
                                             __loc__start__pos 
                                             __loc__end__buf  __loc__end__pos
                                              ->
                                             let _loc =
                                               locate __loc__start__buf
                                                 __loc__start__pos
                                                 __loc__end__buf
                                                 __loc__end__pos in
                                             (mn, mt, _loc)))))))))
                     (Decap.fsequence
                        (Decap.apply_position
                           (fun x  str  pos  str'  pos'  ->
                              ((locate str pos str' pos'), x))
                           (Decap.option None
                              (Decap.apply (fun x  -> Some x)
                                 (Decap.sequence (Decap.string ":" ":")
                                    module_type (fun _  mt  -> mt)))))
                        (Decap.sequence (Decap.string "=" "=")
                           (Decap.apply_position
                              (fun x  str  pos  str'  pos'  ->
                                 ((locate str pos str' pos'), x)) module_expr)
                           (fun _  me  ->
                              let (_loc_me,me) = me in
                              fun mt  ->
                                let (_loc_mt,mt) = mt in
                                fun l  mn  __loc__start__buf 
                                  __loc__start__pos  __loc__end__buf 
                                  __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  let me =
                                    match mt with
                                    | None  -> me
                                    | Some mt ->
                                        mexpr_loc (merge2 _loc_mt _loc_me)
                                          (Pmod_constraint (me, mt)) in
                                  let me =
                                    List.fold_left
                                      (fun acc  (mn,mt,_loc)  ->
                                         mexpr_loc (merge2 _loc _loc_me)
                                           (Pmod_functor (mn, mt, acc))) me
                                      (List.rev l) in
                                  let (name,_,me) =
                                    module_binding _loc mn None me in
                                  loc_str _loc (Pstr_module (name, me))))));
                Decap.fsequence_position type_kw
                  (Decap.fsequence
                     (Decap.apply_position
                        (fun x  str  pos  str'  pos'  ->
                           ((locate str pos str' pos'), x)) modtype_name)
                     (Decap.sequence (Decap.string "=" "=") module_type
                        (fun _  mt  mn  ->
                           let (_loc_mn,mn) = mn in
                           fun _default_0  __loc__start__buf 
                             __loc__start__pos  __loc__end__buf 
                             __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos in
                             loc_str _loc
                               (Pstr_modtype ((id_loc mn _loc_mn), mt)))))])
             (fun _default_0  r  -> r);
           Decap.fsequence_position open_kw
             (Decap.fsequence override_flag
                (Decap.sequence
                   (Decap.apply_position
                      (fun x  str  pos  str'  pos'  ->
                         ((locate str pos str' pos'), x)) module_path)
                   post_item_attributes
                   (fun m  ->
                      let (_loc_m,m) = m in
                      fun a  o  _default_0  __loc__start__buf 
                        __loc__start__pos  __loc__end__buf  __loc__end__pos 
                        ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_str _loc (Pstr_open (o, (id_loc m _loc_m))))));
           Decap.fsequence_position include_kw
             (Decap.sequence module_expr post_item_attributes
                (fun me  a  _default_0  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   loc_str _loc (Pstr_include me)));
           Decap.sequence_position class_kw
             (Decap.alternatives
                [Decap.apply (fun ctd  -> Pstr_class_type ctd)
                   classtype_definition;
                Decap.apply (fun cds  -> Pstr_class cds) class_definition])
             (fun _default_0  r  __loc__start__buf  __loc__start__pos 
                __loc__end__buf  __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_str _loc r);
           Decap.fsequence_position (Decap.string "$struct:" "$struct:")
             (Decap.sequence (Decap.ignore_next_blank expression)
                (Decap.char '$' '$')
                (fun e  _  _  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   let open Quote in
                     pstr_antiquotation _loc
                       (function
                        | Quote_pstr  ->
                            let e_loc = exp_ident _loc "_loc" in
                            quote_apply e_loc _loc (pa_ast "loc_str")
                              [quote_location_t e_loc _loc _loc;
                              quote_const e_loc _loc
                                (parsetree "Pstr_include")
                                [quote_apply e_loc _loc (pa_ast "mexpr_loc")
                                   [quote_location_t e_loc _loc _loc;
                                   quote_const e_loc _loc
                                     (parsetree "Pmod_structure") [e]]]]
                        | _ -> failwith "Bad antiquotation...")))])
    let structure_item_aux = Decap.declare_grammar "structure_item_aux"
    let _ =
      Decap.set_grammar structure_item_aux
        (Decap.alternatives
           [Decap.apply (fun _  -> []) (Decap.empty ());
           Decap.apply_position
             (fun e  ->
                let (_loc_e,e) = e in
                fun __loc__start__buf  __loc__start__pos  __loc__end__buf 
                  __loc__end__pos  ->
                  let _loc =
                    locate __loc__start__buf __loc__start__pos
                      __loc__end__buf __loc__end__pos in
                  (attach_str _loc) @ [loc_str _loc_e (pstr_eval e)])
             (Decap.apply_position
                (fun x  str  pos  str'  pos'  ->
                   ((locate str pos str' pos'), x)) expression);
           Decap.fsequence structure_item_aux
             (Decap.sequence (Decap.option () double_semi_col)
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x))
                   (alternatives extra_structure))
                (fun _default_0  e  ->
                   let (_loc_e,e) = e in
                   fun s1  ->
                     List.rev_append e
                       (List.rev_append (attach_str _loc_e) s1)));
           Decap.fsequence structure_item_aux
             (Decap.sequence (Decap.option () double_semi_col)
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x)) structure_item_base)
                (fun _default_0  s2  ->
                   let (_loc_s2,s2) = s2 in
                   fun s1  -> s2 :: (List.rev_append (attach_str _loc_s2) s1)));
           Decap.fsequence structure_item_aux
             (Decap.sequence double_semi_col
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x)) expression)
                (fun _default_0  e  ->
                   let (_loc_e,e) = e in
                   fun s1  -> (loc_str _loc_e (pstr_eval e)) ::
                     (List.rev_append (attach_str _loc_e) s1)))])
    let _ =
      set_grammar structure_item
        (Decap.sequence structure_item_aux (Decap.option () double_semi_col)
           (fun l  _default_0  -> List.rev l))
    let _ =
      set_grammar structure_item_simple
        (Decap.apply List.rev
           (Decap.fixpoint []
              (Decap.apply (fun x  y  -> x :: y) structure_item_base)))
    let signature_item_base = Decap.declare_grammar "signature_item_base"
    let _ =
      Decap.set_grammar signature_item_base
        (Decap.alternatives
           [Decap.fsequence_position val_kw
              (Decap.fsequence
                 (Decap.apply_position
                    (fun x  str  pos  str'  pos'  ->
                       ((locate str pos str' pos'), x)) value_name)
                 (Decap.fsequence (Decap.string ":" ":")
                    (Decap.sequence typexpr post_item_attributes
                       (fun ty  a  _  n  ->
                          let (_loc_n,n) = n in
                          fun _default_0  __loc__start__buf 
                            __loc__start__pos  __loc__end__buf 
                            __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            loc_sig _loc
                              (psig_value ~attributes:(attach_attrib _loc a)
                                 _loc (id_loc n _loc_n) ty [])))));
           Decap.fsequence_position external_kw
             (Decap.fsequence
                (Decap.apply_position
                   (fun x  str  pos  str'  pos'  ->
                      ((locate str pos str' pos'), x)) value_name)
                (Decap.fsequence (Decap.string ":" ":")
                   (Decap.fsequence typexpr
                      (Decap.fsequence (Decap.string "=" "=")
                         (Decap.sequence
                            (Decap.apply List.rev
                               (Decap.fixpoint []
                                  (Decap.apply (fun x  y  -> x :: y)
                                     string_litteral))) post_item_attributes
                            (fun ls  a  _  ty  _  n  ->
                               let (_loc_n,n) = n in
                               fun _default_0  __loc__start__buf 
                                 __loc__start__pos  __loc__end__buf 
                                 __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos in
                                 let l = List.length ls in
                                 if (l < 1) || (l > 3) then give_up "";
                                 loc_sig _loc
                                   (psig_value
                                      ~attributes:(attach_attrib _loc a) _loc
                                      (id_loc n _loc_n) ty ls)))))));
           Decap.apply_position
             (fun td  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_sig _loc (Psig_type td)) type_definition;
           Decap.sequence_position exception_declaration post_item_attributes
             (fun ((name,ed,_loc') as _default_0)  a  __loc__start__buf 
                __loc__start__pos  __loc__end__buf  __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_sig _loc (Psig_exception (name, ed)));
           Decap.fsequence_position
             (Decap.apply_position
                (fun _default_0  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   attach_sig _loc) module_kw)
             (Decap.fsequence rec_kw
                (Decap.fsequence
                   (Decap.apply_position
                      (fun x  str  pos  str'  pos'  ->
                         ((locate str pos str' pos'), x)) module_name)
                   (Decap.fsequence (Decap.string ":" ":")
                      (Decap.fsequence module_type
                         (Decap.sequence
                            (Decap.apply_position
                               (fun x  str  pos  str'  pos'  ->
                                  ((locate str pos str' pos'), x))
                               post_item_attributes)
                            (Decap.apply List.rev
                               (Decap.fixpoint []
                                  (Decap.apply (fun x  y  -> x :: y)
                                     (Decap.fsequence_position and_kw
                                        (Decap.fsequence module_name
                                           (Decap.fsequence
                                              (Decap.string ":" ":")
                                              (Decap.sequence module_type
                                                 post_item_attributes
                                                 (fun mt  a  _  mn 
                                                    _default_0 
                                                    __loc__start__buf 
                                                    __loc__start__pos 
                                                    __loc__end__buf 
                                                    __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    module_declaration
                                                      ~attributes:(attach_attrib
                                                                    _loc a)
                                                      _loc mn mt))))))))
                            (fun a  ->
                               let (_loc_a,a) = a in
                               fun ms  mt  _  mn  ->
                                 let (_loc_mn,mn) = mn in
                                 fun _default_0  _default_1 
                                   __loc__start__buf  __loc__start__pos 
                                   __loc__end__buf  __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos in
                                   let loc_first = merge2 _loc_mn _loc_a in
                                   let m =
                                     module_declaration
                                       ~attributes:(attach_attrib loc_first a)
                                       loc_first mn mt in
                                   loc_sig _loc (Psig_recmodule (m :: ms))))))));
           Decap.sequence_position module_kw
             (Decap.alternatives
                [Decap.fsequence_position module_name
                   (Decap.fsequence
                      (Decap.apply List.rev
                         (Decap.fixpoint []
                            (Decap.apply (fun x  y  -> x :: y)
                               (Decap.fsequence_position
                                  (Decap.string "(" "(")
                                  (Decap.fsequence module_name
                                     (Decap.fsequence (Decap.string ":" ":")
                                        (Decap.sequence module_type
                                           (Decap.string ")" ")")
                                           (fun mt  _  _  mn  _ 
                                              __loc__start__buf 
                                              __loc__start__pos 
                                              __loc__end__buf 
                                              __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              (mn, mt, _loc)))))))))
                      (Decap.fsequence (Decap.string ":" ":")
                         (Decap.sequence
                            (Decap.apply_position
                               (fun x  str  pos  str'  pos'  ->
                                  ((locate str pos str' pos'), x))
                               module_type) post_item_attributes
                            (fun mt  ->
                               let (_loc_mt,mt) = mt in
                               fun a  _  l  mn  __loc__start__buf 
                                 __loc__start__pos  __loc__end__buf 
                                 __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos in
                                 let mt =
                                   List.fold_left
                                     (fun acc  (mn,mt,_loc)  ->
                                        mtyp_loc (merge2 _loc _loc_mt)
                                          (Pmty_functor (mn, mt, acc))) mt
                                     (List.rev l) in
                                 let (a,b) = module_declaration _loc mn mt in
                                 Psig_module (a, b)))));
                Decap.fsequence type_kw
                  (Decap.fsequence
                     (Decap.apply_position
                        (fun x  str  pos  str'  pos'  ->
                           ((locate str pos str' pos'), x)) modtype_name)
                     (Decap.sequence
                        (Decap.option None
                           (Decap.apply (fun x  -> Some x)
                              (Decap.sequence (Decap.string "=" "=")
                                 module_type (fun _  mt  -> mt))))
                        post_item_attributes
                        (fun mt  a  mn  ->
                           let (_loc_mn,mn) = mn in
                           fun _default_0  ->
                             let mt =
                               match mt with
                               | None  -> Pmodtype_abstract
                               | Some mt -> Pmodtype_manifest mt in
                             Psig_modtype ((id_loc mn _loc_mn), mt))))])
             (fun _default_0  r  __loc__start__buf  __loc__start__pos 
                __loc__end__buf  __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_sig _loc r);
           Decap.fsequence_position open_kw
             (Decap.fsequence override_flag
                (Decap.sequence
                   (Decap.apply_position
                      (fun x  str  pos  str'  pos'  ->
                         ((locate str pos str' pos'), x)) module_path)
                   post_item_attributes
                   (fun m  ->
                      let (_loc_m,m) = m in
                      fun a  o  _default_0  __loc__start__buf 
                        __loc__start__pos  __loc__end__buf  __loc__end__pos 
                        ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_sig _loc (Psig_open (o, (id_loc m _loc_m))))));
           Decap.fsequence_position include_kw
             (Decap.sequence module_type post_item_attributes
                (fun me  a  _default_0  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   loc_sig _loc (Psig_include me)));
           Decap.sequence_position class_kw
             (Decap.alternatives
                [Decap.apply (fun ctd  -> Psig_class_type ctd)
                   classtype_definition;
                Decap.apply (fun cs  -> Psig_class cs) class_specification])
             (fun _default_0  r  __loc__start__buf  __loc__start__pos 
                __loc__end__buf  __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                loc_sig _loc r);
           Decap.fsequence_position
             (Decap.ignore_next_blank (Decap.char '$' '$'))
             (Decap.sequence (Decap.ignore_next_blank expression)
                (Decap.char '$' '$')
                (fun e  _  dol  __loc__start__buf  __loc__start__pos 
                   __loc__end__buf  __loc__end__pos  ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   let open Quote in
                     psig_antiquotation _loc
                       (function
                        | Quote_psig  -> e
                        | _ -> failwith "Bad antiquotation...")))])
    let _ =
      set_grammar signature_item
        (Decap.alternatives
           [Decap.apply_position
              (fun e  __loc__start__buf  __loc__start__pos  __loc__end__buf 
                 __loc__end__pos  ->
                 let _loc =
                   locate __loc__start__buf __loc__start__pos __loc__end__buf
                     __loc__end__pos in
                 (attach_sig _loc) @ e) (alternatives extra_signature);
           Decap.sequence_position signature_item_base
             (Decap.option None
                (Decap.apply (fun x  -> Some x) double_semi_col))
             (fun s  _  __loc__start__buf  __loc__start__pos  __loc__end__buf
                 __loc__end__pos  ->
                let _loc =
                  locate __loc__start__buf __loc__start__pos __loc__end__buf
                    __loc__end__pos in
                (attach_sig _loc) @ [s])])
    exception Top_Exit
    let top_phrase = Decap.declare_grammar "top_phrase"
    let _ =
      Decap.set_grammar top_phrase
        (Decap.alternatives
           [Decap.fsequence
              (Decap.option None
                 (Decap.apply (fun x  -> Some x) (Decap.char ';' ';')))
              (Decap.sequence
                 (Decap.apply List.rev
                    (Decap.fixpoint1 []
                       (Decap.apply (fun x  y  -> x :: y) structure_item_base)))
                 double_semi_col
                 (fun l  _default_0  _default_1  -> Ptop_def l));
           Decap.sequence
             (Decap.option None
                (Decap.apply (fun x  -> Some x) (Decap.char ';' ';')))
             (Decap.eof ()) (fun _default_0  _  -> raise Top_Exit)])
  end
