open Input
open Earley
open Charset
open Ast_helper
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
    let uident = Earley.declare_grammar "uident"
    let _ =
      Earley.set_grammar uident
        (Earley.alternatives
           [ouident;
           Earley.fsequence_position (Earley.string "$uid:" "$uid:")
             (Earley.sequence (Earley.ignore_next_blank expression)
                (Earley.char '$' '$')
                (fun e  ->
                   fun _  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               Quote.string_antiquotation _loc e))])
    let olident = lident
    let lident = Earley.declare_grammar "lident"
    let _ =
      Earley.set_grammar lident
        (Earley.alternatives
           [olident;
           Earley.fsequence_position (Earley.string "$lid:" "$lid:")
             (Earley.sequence (Earley.ignore_next_blank expression)
                (Earley.char '$' '$')
                (fun e  ->
                   fun _  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               Quote.string_antiquotation _loc e))])
    let oident = ident
    let ident = Earley.declare_grammar "ident"
    let _ =
      Earley.set_grammar ident
        (Earley.alternatives
           [oident;
           Earley.fsequence_position (Earley.string "$ident:" "$ident:")
             (Earley.sequence (Earley.ignore_next_blank expression)
                (Earley.char '$' '$')
                (fun e  ->
                   fun _  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
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
          | Ptyp_object (lst,cl) ->
              Ptyp_object ((List.map loop_core_field lst), cl)
          | Ptyp_class (longident,lst) ->
              Ptyp_class (longident, (List.map loop lst))
          | Ptyp_extension _ as ty -> ty
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
      and loop_core_field (str,attr,ty) = (str, attr, (loop ty))
      and loop_row_field =
        function
        | Rtag (label,attr,flag,lst) ->
            Rtag (label, attr, flag, (List.map loop lst))
        | Rinherit t -> Rinherit (loop t) in
      loop t
    let wrap_type_annotation _loc newtypes core_type body =
      let exp = loc_expr _loc (pexp_constraint (body, core_type)) in
      let exp =
        List.fold_right
          (fun newtype  ->
             fun exp  -> loc_expr _loc (Pexp_newtype (newtype, exp)))
          newtypes exp in
      (exp,
        (loc_typ _loc
           (Ptyp_poly (newtypes, (varify_constructors newtypes core_type)))))
    let float_litteral = Earley.apply fst Pa_lexing.float_litteral
    let _ = set_grammar char_litteral Pa_lexing.char_litteral
    let _ =
      set_grammar string_litteral
        (Earley.apply fst Pa_lexing.string_litteral)
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
       fn t; Buffer.contents b : string)
    let label_name = lident
    let label = Earley.declare_grammar "label"
    let _ =
      Earley.set_grammar label
        (Earley.fsequence (Earley.ignore_next_blank (Earley.char '~' '~'))
           (Earley.sequence (Earley.ignore_next_blank label_name) no_colon
              (fun ln  -> fun _default_0  -> fun _  -> ln)))
    let opt_label = Earley.declare_grammar "opt_label"
    let _ =
      Earley.set_grammar opt_label
        (Earley.fsequence (Earley.ignore_next_blank (Earley.char '?' '?'))
           (Earley.sequence (Earley.ignore_next_blank label_name) no_colon
              (fun ln  -> fun _default_0  -> fun _  -> ln)))
    let ty_label = Earley.declare_grammar "ty_label"
    let _ =
      Earley.set_grammar ty_label
        (Earley.fsequence (Earley.ignore_next_blank (Earley.char '~' '~'))
           (Earley.sequence (Earley.ignore_next_blank lident)
              (Earley.char ':' ':')
              (fun s  -> fun _  -> fun _  -> labelled s)))
    let ty_opt_label = Earley.declare_grammar "ty_opt_label"
    let _ =
      Earley.set_grammar ty_opt_label
        (Earley.fsequence (Earley.ignore_next_blank (Earley.char '?' '?'))
           (Earley.sequence (Earley.ignore_next_blank lident)
              (Earley.char ':' ':')
              (fun s  -> fun _  -> fun _  -> optional s)))
    let maybe_opt_label = Earley.declare_grammar "maybe_opt_label"
    let _ =
      Earley.set_grammar maybe_opt_label
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x) (Earley.string "?" "?")))
           label_name
           (fun o  ->
              fun ln  -> if o = None then labelled ln else optional ln))
    let operator_name = Earley.declare_grammar "operator_name"
    let _ =
      Earley.set_grammar operator_name
        (Earley.alternatives
           [alternatives (List.map infix_symbol infix_prios);
           alternatives (List.map prefix_symbol prefix_prios)])
    let value_name = Earley.declare_grammar "value_name"
    let _ =
      Earley.set_grammar value_name
        (Earley.alternatives
           [lident;
           Earley.fsequence (Earley.char '(' '(')
             (Earley.sequence operator_name (Earley.char ')' ')')
                (fun op  -> fun _  -> fun _  -> op))])
    let constr_name = uident
    let tag_name = Earley.declare_grammar "tag_name"
    let _ =
      Earley.set_grammar tag_name
        (Earley.sequence (Earley.string "`" "`") ident
           (fun _  -> fun c  -> c))
    let typeconstr_name = lident
    let field_name = lident
    let smodule_name = uident
    let module_name = Earley.declare_grammar "module_name"
    let _ =
      Earley.set_grammar module_name
        (Earley.apply_position
           (fun u  ->
              fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
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
      Earley.grammar_family "module_path_suit_aux"
    let _ =
      module_path_suit_aux__set__grammar
        (fun allow_app  ->
           Earley.alternatives
             (let y =
                [Earley.sequence (Earley.string "." ".") smodule_name
                   (fun _  -> fun m  -> fun acc  -> Ldot (acc, m))] in
              if allow_app
              then
                (Earley.fsequence (Earley.string "(" "(")
                   (Earley.sequence (module_path_gen true)
                      (Earley.string ")" ")")
                      (fun m'  ->
                         fun _  -> fun _  -> fun a  -> Lapply (a, m'))))
                :: y
              else y))
    let _ =
      set_module_path_suit
        (fun allow_app  ->
           Earley.alternatives
             [Earley.sequence (module_path_suit_aux allow_app)
                (module_path_suit allow_app)
                (fun f  -> fun g  -> fun acc  -> g (f acc));
             Earley.apply (fun _  -> fun acc  -> acc) (Earley.empty ())])
    let _ =
      set_module_path_gen
        (fun allow_app  ->
           Earley.sequence smodule_name (module_path_suit allow_app)
             (fun m  -> fun s  -> s (Lident m)))
    let module_path = module_path_gen false
    let extended_module_path = module_path_gen true
    let _ =
      set_grammar value_path
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence module_path (Earley.string "." ".")
                    (fun m  -> fun _  -> m)))) value_name
           (fun mp  ->
              fun vn  ->
                match mp with | None  -> Lident vn | Some p -> Ldot (p, vn)))
    let constr = Earley.declare_grammar "constr"
    let _ =
      Earley.set_grammar constr
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence module_path (Earley.string "." ".")
                    (fun m  -> fun _  -> m)))) constr_name
           (fun mp  ->
              fun cn  ->
                match mp with | None  -> Lident cn | Some p -> Ldot (p, cn)))
    let typeconstr = Earley.declare_grammar "typeconstr"
    let _ =
      Earley.set_grammar typeconstr
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence extended_module_path
                    (Earley.string "." ".") (fun m  -> fun _  -> m))))
           typeconstr_name
           (fun mp  ->
              fun tcn  ->
                match mp with | None  -> Lident tcn | Some p -> Ldot (p, tcn)))
    let field = Earley.declare_grammar "field"
    let _ =
      Earley.set_grammar field
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence module_path (Earley.string "." ".")
                    (fun m  -> fun _  -> m)))) field_name
           (fun mp  ->
              fun fn  ->
                match mp with | None  -> Lident fn | Some p -> Ldot (p, fn)))
    let class_path = Earley.declare_grammar "class_path"
    let _ =
      Earley.set_grammar class_path
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence module_path (Earley.string "." ".")
                    (fun m  -> fun _  -> m)))) class_name
           (fun mp  ->
              fun cn  ->
                match mp with | None  -> Lident cn | Some p -> Ldot (p, cn)))
    let modtype_path = Earley.declare_grammar "modtype_path"
    let _ =
      Earley.set_grammar modtype_path
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence extended_module_path
                    (Earley.string "." ".") (fun m  -> fun _  -> m))))
           modtype_name
           (fun mp  ->
              fun mtn  ->
                match mp with | None  -> Lident mtn | Some p -> Ldot (p, mtn)))
    let classtype_path = Earley.declare_grammar "classtype_path"
    let _ =
      Earley.set_grammar classtype_path
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence extended_module_path
                    (Earley.string "." ".") (fun m  -> fun _  -> m))))
           class_name
           (fun mp  ->
              fun cn  ->
                match mp with | None  -> Lident cn | Some p -> Ldot (p, cn)))
    let opt_variance = Earley.declare_grammar "opt_variance"
    let _ =
      Earley.set_grammar opt_variance
        (Earley.apply
           (fun v  ->
              match v with
              | None  -> Invariant
              | Some "+" -> Covariant
              | Some "-" -> Contravariant
              | _ -> assert false)
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (EarleyStr.regexp "[+-]" (fun groupe  -> groupe 0)))))
    let override_flag = Earley.declare_grammar "override_flag"
    let _ =
      Earley.set_grammar override_flag
        (Earley.apply (fun o  -> if o <> None then Override else Fresh)
           (Earley.option None
              (Earley.apply (fun x  -> Some x) (Earley.string "!" "!"))))
    let attr_id = Earley.declare_grammar "attr_id"
    let _ =
      Earley.set_grammar attr_id
        (Earley.sequence_position ident
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.sequence (Earley.char '.' '.') ident
                       (fun _  -> fun id  -> id)))))
           (fun id  ->
              fun l  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        id_loc (String.concat "." (id :: l)) _loc))
    let payload = Earley.declare_grammar "payload"
    let _ =
      Earley.set_grammar payload
        (Earley.alternatives
           [Earley.apply (fun s  -> PStr s) structure;
           Earley.sequence (Earley.char ':' ':') typexpr
             (fun _  -> fun t  -> PTyp t);
           Earley.fsequence (Earley.char '?' '?')
             (Earley.sequence pattern
                (Earley.option None
                   (Earley.apply (fun x  -> Some x)
                      (Earley.sequence (Earley.string "when" "when")
                         expression (fun _  -> fun e  -> e))))
                (fun p  -> fun e  -> fun _  -> PPat (p, e)))])
    let attribute = Earley.declare_grammar "attribute"
    let _ =
      Earley.set_grammar attribute
        (Earley.fsequence (Earley.string "[@" "[@")
           (Earley.sequence attr_id payload
              (fun id  -> fun p  -> fun _  -> (id, p))))
    let attributes = Earley.declare_grammar "attributes"
    let _ =
      Earley.set_grammar attributes
        (Earley.apply List.rev
           (Earley.fixpoint []
              (Earley.apply (fun x  -> fun y  -> x :: y) attribute)))
    let ext_attributes = Earley.declare_grammar "ext_attributes"
    let _ =
      Earley.set_grammar ext_attributes
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence (Earley.char '%' '%') attribute
                    (fun _  -> fun a  -> a)))) attributes
           (fun a  -> fun l  -> (a, l)))
    let post_item_attributes = Earley.declare_grammar "post_item_attributes"
    let _ =
      Earley.set_grammar post_item_attributes
        (Earley.apply List.rev
           (Earley.fixpoint []
              (Earley.apply (fun x  -> fun y  -> x :: y)
                 (Earley.fsequence (Earley.string "[@@" "[@@")
                    (Earley.fsequence attr_id
                       (Earley.sequence payload (Earley.char ']' ']')
                          (fun p  -> fun _  -> fun id  -> fun _  -> (id, p))))))))
    let ext_attributes = Earley.declare_grammar "ext_attributes"
    let _ =
      Earley.set_grammar ext_attributes
        (Earley.apply List.rev
           (Earley.fixpoint []
              (Earley.apply (fun x  -> fun y  -> x :: y)
                 (Earley.fsequence (Earley.string "[@@@" "[@@@")
                    (Earley.fsequence attr_id
                       (Earley.sequence payload (Earley.char ']' ']')
                          (fun p  -> fun _  -> fun id  -> fun _  -> (id, p))))))))
    let extension = Earley.declare_grammar "extension"
    let _ =
      Earley.set_grammar extension
        (Earley.fsequence (Earley.string "[%" "[%")
           (Earley.fsequence attr_id
              (Earley.sequence payload (Earley.char ']' ']')
                 (fun p  -> fun _  -> fun id  -> fun _  -> (id, p)))))
    let item_extension = Earley.declare_grammar "item_extension"
    let _ =
      Earley.set_grammar item_extension
        (Earley.fsequence (Earley.string "[%%" "[%%")
           (Earley.fsequence attr_id
              (Earley.sequence payload (Earley.char ']' ']')
                 (fun p  -> fun _  -> fun id  -> fun _  -> (id, p)))))
    let only_poly_typexpr = Earley.declare_grammar "only_poly_typexpr"
    let _ =
      Earley.set_grammar only_poly_typexpr
        (Earley.fsequence_position
           (Earley.apply List.rev
              (Earley.fixpoint1 []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.sequence (Earley.string "'" "'") ident
                       (fun _  -> fun id  -> id)))))
           (Earley.sequence (Earley.string "." ".") typexpr
              (fun _  ->
                 fun te  ->
                   fun ids  ->
                     fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos in
                             loc_typ _loc (Ptyp_poly (ids, te)))))
    let poly_typexpr = Earley.declare_grammar "poly_typexpr"
    let _ =
      Earley.set_grammar poly_typexpr
        (Earley.alternatives
           [Earley.fsequence_position
              (Earley.apply List.rev
                 (Earley.fixpoint1 []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.sequence (Earley.string "'" "'") ident
                          (fun _  -> fun id  -> id)))))
              (Earley.sequence (Earley.string "." ".") typexpr
                 (fun _  ->
                    fun te  ->
                      fun ids  ->
                        fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos in
                                loc_typ _loc (Ptyp_poly (ids, te))));
           typexpr])
    let poly_syntax_typexpr = Earley.declare_grammar "poly_syntax_typexpr"
    let _ =
      Earley.set_grammar poly_syntax_typexpr
        (Earley.fsequence type_kw
           (Earley.fsequence
              (Earley.apply List.rev
                 (Earley.fixpoint1 []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       typeconstr_name)))
              (Earley.sequence (Earley.string "." ".") typexpr
                 (fun _  ->
                    fun te  -> fun ids  -> fun _default_0  -> (ids, te)))))
    let method_type = Earley.declare_grammar "method_type"
    let _ =
      Earley.set_grammar method_type
        (Earley.fsequence method_name
           (Earley.sequence (Earley.string ":" ":") poly_typexpr
              (fun _  -> fun pte  -> fun mn  -> (mn, [], pte))))
    let tag_spec = Earley.declare_grammar "tag_spec"
    let _ =
      Earley.set_grammar tag_spec
        (Earley.alternatives
           [Earley.sequence tag_name
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.fsequence of_kw
                       (Earley.sequence
                          (Earley.option None
                             (Earley.apply (fun x  -> Some x)
                                (Earley.char '&' '&'))) typexpr
                          (fun _default_1  ->
                             fun _default_0  ->
                               fun _  -> (_default_1, _default_0))))))
              (fun tn  ->
                 fun te  ->
                   let (amp,t) =
                     match te with
                     | None  -> (true, [])
                     | Some (amp,l) -> ((amp <> None), [l]) in
                   Rtag (tn, [], amp, t));
           Earley.apply (fun te  -> Rinherit te) typexpr])
    let tag_spec_first = Earley.declare_grammar "tag_spec_first"
    let _ =
      Earley.set_grammar tag_spec_first
        (Earley.alternatives
           [Earley.sequence tag_name
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.fsequence of_kw
                       (Earley.sequence
                          (Earley.option None
                             (Earley.apply (fun x  -> Some x)
                                (Earley.char '&' '&'))) typexpr
                          (fun _default_1  ->
                             fun _default_0  ->
                               fun _  -> (_default_1, _default_0))))))
              (fun tn  ->
                 fun te  ->
                   let (amp,t) =
                     match te with
                     | None  -> (true, [])
                     | Some (amp,l) -> ((amp <> None), [l]) in
                   [Rtag (tn, [], amp, t)]);
           Earley.fsequence
             (Earley.option None (Earley.apply (fun x  -> Some x) typexpr))
             (Earley.sequence (Earley.string "|" "|") tag_spec
                (fun _  ->
                   fun ts  ->
                     fun te  ->
                       match te with
                       | None  -> [ts]
                       | Some te -> [Rinherit te; ts]))])
    let tag_spec_full = Earley.declare_grammar "tag_spec_full"
    let _ =
      Earley.set_grammar tag_spec_full
        (Earley.alternatives
           [Earley.sequence tag_name
              (Earley.option (true, [])
                 (Earley.fsequence of_kw
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x)
                             (Earley.char '&' '&')))
                       (Earley.sequence typexpr
                          (Earley.apply List.rev
                             (Earley.fixpoint []
                                (Earley.apply (fun x  -> fun y  -> x :: y)
                                   (Earley.sequence (Earley.string "&" "&")
                                      typexpr (fun _  -> fun te  -> te)))))
                          (fun te  ->
                             fun tes  ->
                               fun amp  ->
                                 fun _default_0  ->
                                   ((amp <> None), (te :: tes)))))))
              (fun tn  ->
                 fun ((amp,tes) as _default_0)  -> Rtag (tn, [], amp, tes));
           Earley.apply (fun te  -> Rinherit te) typexpr])
    let polymorphic_variant_type : core_type grammar=
      Earley.declare_grammar "polymorphic_variant_type"
    let _ =
      Earley.set_grammar polymorphic_variant_type
        (Earley.alternatives
           [Earley.fsequence_position (Earley.string "[" "[")
              (Earley.fsequence tag_spec_first
                 (Earley.sequence
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             (Earley.sequence (Earley.string "|" "|")
                                tag_spec (fun _  -> fun ts  -> ts)))))
                    (Earley.string "]" "]")
                    (fun tss  ->
                       fun _  ->
                         fun tsf  ->
                           fun _  ->
                             fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     let flag = Closed in
                                     loc_typ _loc
                                       (Ptyp_variant
                                          ((tsf @ tss), flag, None)))));
           Earley.fsequence_position (Earley.string "[>" "[>")
             (Earley.fsequence
                (Earley.option None
                   (Earley.apply (fun x  -> Some x) tag_spec))
                (Earley.sequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            (Earley.sequence (Earley.string "|" "|") tag_spec
                               (fun _  -> fun ts  -> ts)))))
                   (Earley.string "]" "]")
                   (fun tss  ->
                      fun _  ->
                        fun ts  ->
                          fun _  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    let tss =
                                      match ts with
                                      | None  -> tss
                                      | Some ts -> ts :: tss in
                                    let flag = Open in
                                    loc_typ _loc
                                      (Ptyp_variant (tss, flag, None)))));
           Earley.fsequence_position (Earley.string "[<" "[<")
             (Earley.fsequence
                (Earley.option None
                   (Earley.apply (fun x  -> Some x) (Earley.string "|" "|")))
                (Earley.fsequence tag_spec_full
                   (Earley.fsequence
                      (Earley.apply List.rev
                         (Earley.fixpoint []
                            (Earley.apply (fun x  -> fun y  -> x :: y)
                               (Earley.sequence (Earley.string "|" "|")
                                  tag_spec_full (fun _  -> fun tsf  -> tsf)))))
                      (Earley.sequence
                         (Earley.option []
                            (Earley.sequence (Earley.string ">" ">")
                               (Earley.apply List.rev
                                  (Earley.fixpoint1 []
                                     (Earley.apply
                                        (fun x  -> fun y  -> x :: y) tag_name)))
                               (fun _  -> fun tns  -> tns)))
                         (Earley.string "]" "]")
                         (fun tns  ->
                            fun _  ->
                              fun tfss  ->
                                fun tfs  ->
                                  fun _default_0  ->
                                    fun _  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              let flag = Closed in
                                              loc_typ _loc
                                                (Ptyp_variant
                                                   ((tfs :: tfss), flag,
                                                     (Some tns))))))))])
    let package_constraint = Earley.declare_grammar "package_constraint"
    let _ =
      Earley.set_grammar package_constraint
        (Earley.fsequence type_kw
           (Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 typeconstr)
              (Earley.sequence (Earley.char '=' '=') typexpr
                 (fun _  ->
                    fun te  ->
                      fun tc  ->
                        let (_loc_tc,tc) = tc in
                        fun _default_0  ->
                          let tc = id_loc tc _loc_tc in (tc, te)))))
    let package_type = Earley.declare_grammar "package_type"
    let _ =
      Earley.set_grammar package_type
        (Earley.sequence
           (Earley.apply_position
              (fun x  ->
                 fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> ((locate str pos str' pos'), x))
              modtype_path)
           (Earley.option []
              (Earley.fsequence with_kw
                 (Earley.sequence package_constraint
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             (Earley.sequence and_kw package_constraint
                                (fun _  -> fun _default_0  -> _default_0)))))
                    (fun pc  -> fun pcs  -> fun _default_0  -> pc :: pcs))))
           (fun mtp  ->
              let (_loc_mtp,mtp) = mtp in
              fun cs  ->
                let mtp = id_loc mtp _loc_mtp in Ptyp_package (mtp, cs)))
    let opt_present = Earley.declare_grammar "opt_present"
    let _ =
      Earley.set_grammar opt_present
        (Earley.alternatives
           [Earley.fsequence (Earley.string "[>" "[>")
              (Earley.sequence
                 (Earley.apply List.rev
                    (Earley.fixpoint1 []
                       (Earley.apply (fun x  -> fun y  -> x :: y) tag_name)))
                 (Earley.string "]" "]") (fun l  -> fun _  -> fun _  -> l));
           Earley.apply (fun _  -> []) (Earley.empty ())])
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
           Earley.alternatives ((extra_types_grammar lvl) ::
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
                                                      (Earley.fsequence_position
                                                         (Earley.ignore_next_blank
                                                            (Earley.char '$'
                                                               '$'))
                                                         (Earley.fsequence
                                                            (Earley.option
                                                               "type"
                                                               (Earley.sequence
                                                                  (Earley.ignore_next_blank
                                                                    (EarleyStr.regexp
                                                                    ~name:"[a-z]+"
                                                                    "[a-z]+"
                                                                    (fun
                                                                    groupe 
                                                                    ->
                                                                    groupe 0)))
                                                                  (Earley.char
                                                                    ':' ':')
                                                                  (fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    _default_0)))
                                                            (Earley.sequence
                                                               (Earley.ignore_next_blank
                                                                  expression)
                                                               (Earley.char
                                                                  '$' '$')
                                                               (fun e  ->
                                                                  fun _  ->
                                                                    fun aq 
                                                                    ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    () in
                                                                    Quote.ptyp_antiquotation
                                                                    _loc f))))
                                                      :: y
                                                    else y in
                                                  if lvl = DashType
                                                  then
                                                    (Earley.fsequence_position
                                                       (typexpr_lvl DashType)
                                                       (Earley.sequence
                                                          (Earley.string "#"
                                                             "#")
                                                          (Earley.apply_position
                                                             (fun x  ->
                                                                fun str  ->
                                                                  fun pos  ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                             class_path)
                                                          (fun _  ->
                                                             fun cp  ->
                                                               let (_loc_cp,cp)
                                                                 = cp in
                                                               fun te  ->
                                                                 fun
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
                                                                    let cp =
                                                                    id_loc cp
                                                                    _loc_cp in
                                                                    loc_typ
                                                                    _loc
                                                                    (Ptyp_class
                                                                    (cp,
                                                                    [te])))))
                                                    :: y
                                                  else y in
                                                if lvl = As
                                                then
                                                  (Earley.fsequence_position
                                                     (typexpr_lvl As)
                                                     (Earley.fsequence as_kw
                                                        (Earley.sequence
                                                           (Earley.string "'"
                                                              "'") ident
                                                           (fun _  ->
                                                              fun id  ->
                                                                fun
                                                                  _default_0 
                                                                  ->
                                                                  fun te  ->
                                                                    fun
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
                                                                    loc_typ
                                                                    _loc
                                                                    (Ptyp_alias
                                                                    (te, id))))))
                                                  :: y
                                                else y in
                                              if lvl = ProdType
                                              then
                                                (Earley.sequence_position
                                                   (typexpr_lvl
                                                      (next_type_prio
                                                         ProdType))
                                                   (Earley.apply List.rev
                                                      (Earley.fixpoint1 []
                                                         (Earley.apply
                                                            (fun x  ->
                                                               fun y  -> x ::
                                                                 y)
                                                            (Earley.sequence
                                                               (Earley.alternatives
                                                                  [Earley.apply
                                                                    (fun _ 
                                                                    -> ())
                                                                    (Earley.char
                                                                    '*' '*');
                                                                  Earley.apply
                                                                    (
                                                                    fun _  ->
                                                                    ())
                                                                    (
                                                                    Earley.string
                                                                    "\195\151"
                                                                    "\195\151")])
                                                               (typexpr_lvl
                                                                  (next_type_prio
                                                                    ProdType))
                                                               (fun _  ->
                                                                  fun te  ->
                                                                    te)))))
                                                   (fun te  ->
                                                      fun tes  ->
                                                        fun __loc__start__buf
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
                                                                loc_typ _loc
                                                                  (Ptyp_tuple
                                                                    (te ::
                                                                    tes))))
                                                :: y
                                              else y in
                                            if lvl = AtomType
                                            then
                                              (Earley.fsequence_position
                                                 (Earley.string "(" "(")
                                                 (Earley.fsequence typexpr
                                                    (Earley.fsequence
                                                       (Earley.apply List.rev
                                                          (Earley.fixpoint []
                                                             (Earley.apply
                                                                (fun x  ->
                                                                   fun y  ->
                                                                    x :: y)
                                                                (Earley.sequence
                                                                   (Earley.string
                                                                    "," ",")
                                                                   typexpr
                                                                   (fun _  ->
                                                                    fun te 
                                                                    -> te)))))
                                                       (Earley.fsequence
                                                          (Earley.string ")"
                                                             ")")
                                                          (Earley.sequence
                                                             (Earley.string
                                                                "#" "#")
                                                             (Earley.apply_position
                                                                (fun x  ->
                                                                   fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                class_path)
                                                             (fun _  ->
                                                                fun cp  ->
                                                                  let 
                                                                    (_loc_cp,cp)
                                                                    = cp in
                                                                  fun _  ->
                                                                    fun tes 
                                                                    ->
                                                                    fun te 
                                                                    ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let cp =
                                                                    id_loc cp
                                                                    _loc_cp in
                                                                    loc_typ
                                                                    _loc
                                                                    (Ptyp_class
                                                                    (cp, (te
                                                                    :: tes)))))))))
                                              :: y
                                            else y in
                                          if lvl = AtomType
                                          then
                                            (Earley.sequence_position
                                               (Earley.string "#" "#")
                                               (Earley.apply_position
                                                  (fun x  ->
                                                     fun str  ->
                                                       fun pos  ->
                                                         fun str'  ->
                                                           fun pos'  ->
                                                             ((locate str pos
                                                                 str' pos'),
                                                               x)) class_path)
                                               (fun _  ->
                                                  fun cp  ->
                                                    let (_loc_cp,cp) = cp in
                                                    fun __loc__start__buf  ->
                                                      fun __loc__start__pos 
                                                        ->
                                                        fun __loc__end__buf 
                                                          ->
                                                          fun __loc__end__pos
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
                                                            loc_typ _loc
                                                              (Ptyp_class
                                                                 (cp, []))))
                                            :: y
                                          else y in
                                        if lvl = AtomType
                                        then
                                          (Earley.fsequence_position
                                             (Earley.string "<" "<")
                                             (Earley.fsequence method_type
                                                (Earley.fsequence
                                                   (Earley.apply List.rev
                                                      (Earley.fixpoint []
                                                         (Earley.apply
                                                            (fun x  ->
                                                               fun y  -> x ::
                                                                 y)
                                                            (Earley.sequence
                                                               semi_col
                                                               method_type
                                                               (fun _  ->
                                                                  fun mt  ->
                                                                    mt)))))
                                                   (Earley.sequence
                                                      (Earley.option None
                                                         (Earley.apply
                                                            (fun x  -> Some x)
                                                            (Earley.sequence
                                                               semi_col
                                                               (Earley.option
                                                                  None
                                                                  (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Earley.string
                                                                    ".." "..")))
                                                               (fun _  ->
                                                                  fun rv  ->
                                                                    rv))))
                                                      (Earley.char '>' '>')
                                                      (fun rv  ->
                                                         fun _  ->
                                                           fun mts  ->
                                                             fun mt  ->
                                                               fun _  ->
                                                                 fun
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
                                                                    let ml =
                                                                    if
                                                                    (rv =
                                                                    None) ||
                                                                    (rv =
                                                                    (Some
                                                                    None))
                                                                    then
                                                                    Closed
                                                                    else Open in
                                                                    loc_typ
                                                                    _loc
                                                                    (Ptyp_object
                                                                    ((mt ::
                                                                    mts), ml)))))))
                                          :: y
                                        else y in
                                      if lvl = AtomType
                                      then
                                        (Earley.fsequence_position
                                           (Earley.char '<' '<')
                                           (Earley.sequence
                                              (Earley.option None
                                                 (Earley.apply
                                                    (fun x  -> Some x)
                                                    (Earley.string ".." "..")))
                                              (Earley.char '>' '>')
                                              (fun rv  ->
                                                 fun _  ->
                                                   fun _  ->
                                                     fun __loc__start__buf 
                                                       ->
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
                                                             let ml =
                                                               if rv = None
                                                               then Closed
                                                               else Open in
                                                             loc_typ _loc
                                                               (Ptyp_object
                                                                  ([], ml)))))
                                        :: y
                                      else y in
                                    if lvl = AtomType
                                    then polymorphic_variant_type :: y
                                    else y in
                                  if lvl = AppType
                                  then
                                    (Earley.sequence_position
                                       (typexpr_lvl AppType)
                                       (Earley.apply_position
                                          (fun x  ->
                                             fun str  ->
                                               fun pos  ->
                                                 fun str'  ->
                                                   fun pos'  ->
                                                     ((locate str pos str'
                                                         pos'), x))
                                          typeconstr)
                                       (fun t  ->
                                          fun tc  ->
                                            let (_loc_tc,tc) = tc in
                                            fun __loc__start__buf  ->
                                              fun __loc__start__pos  ->
                                                fun __loc__end__buf  ->
                                                  fun __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    let constr =
                                                      id_loc tc _loc_tc in
                                                    loc_typ _loc
                                                      (Ptyp_constr
                                                         (constr, [t]))))
                                    :: y
                                  else y in
                                if lvl = AppType
                                then
                                  (Earley.fsequence_position
                                     (Earley.char '(' '(')
                                     (Earley.fsequence typexpr
                                        (Earley.fsequence
                                           (Earley.apply List.rev
                                              (Earley.fixpoint1 []
                                                 (Earley.apply
                                                    (fun x  ->
                                                       fun y  -> x :: y)
                                                    (Earley.sequence
                                                       (Earley.char ',' ',')
                                                       typexpr
                                                       (fun _  ->
                                                          fun te  -> te)))))
                                           (Earley.sequence
                                              (Earley.char ')' ')')
                                              (Earley.apply_position
                                                 (fun x  ->
                                                    fun str  ->
                                                      fun pos  ->
                                                        fun str'  ->
                                                          fun pos'  ->
                                                            ((locate str pos
                                                                str' pos'),
                                                              x)) typeconstr)
                                              (fun _  ->
                                                 fun tc  ->
                                                   let (_loc_tc,tc) = tc in
                                                   fun tes  ->
                                                     fun te  ->
                                                       fun _  ->
                                                         fun
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
                                                                 let constr =
                                                                   id_loc tc
                                                                    _loc_tc in
                                                                 loc_typ _loc
                                                                   (Ptyp_constr
                                                                    (constr,
                                                                    (te ::
                                                                    tes))))))))
                                  :: y
                                else y in
                              if lvl = AtomType
                              then
                                (Earley.apply_position
                                   (fun tc  ->
                                      let (_loc_tc,tc) = tc in
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              loc_typ _loc
                                                (Ptyp_constr
                                                   ((id_loc tc _loc_tc), [])))
                                   (Earley.apply_position
                                      (fun x  ->
                                         fun str  ->
                                           fun pos  ->
                                             fun str'  ->
                                               fun pos'  ->
                                                 ((locate str pos str' pos'),
                                                   x)) typeconstr))
                                :: y
                              else y in
                            if lvl = Arr
                            then
                              (Earley.fsequence_position
                                 (typexpr_lvl (next_type_prio Arr))
                                 (Earley.sequence arrow_re (typexpr_lvl Arr)
                                    (fun _default_0  ->
                                       fun te'  ->
                                         fun te  ->
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   loc_typ _loc
                                                     (Ptyp_arrow
                                                        (nolabel, te, te')))))
                              :: y
                            else y in
                          if lvl = Arr
                          then
                            (Earley.fsequence_position label_name
                               (Earley.fsequence (Earley.char ':' ':')
                                  (Earley.fsequence
                                     (typexpr_lvl (next_type_prio Arr))
                                     (Earley.sequence arrow_re
                                        (typexpr_lvl Arr)
                                        (fun _default_0  ->
                                           fun te'  ->
                                             fun te  ->
                                               fun _  ->
                                                 fun ln  ->
                                                   fun __loc__start__buf  ->
                                                     fun __loc__start__pos 
                                                       ->
                                                       fun __loc__end__buf 
                                                         ->
                                                         fun __loc__end__pos 
                                                           ->
                                                           let _loc =
                                                             locate
                                                               __loc__start__buf
                                                               __loc__start__pos
                                                               __loc__end__buf
                                                               __loc__end__pos in
                                                           loc_typ _loc
                                                             (Ptyp_arrow
                                                                ((labelled ln),
                                                                  te, te')))))))
                            :: y
                          else y in
                        if lvl = Arr
                        then
                          (Earley.fsequence_position ty_opt_label
                             (Earley.fsequence
                                (Earley.apply_position
                                   (fun x  ->
                                      fun str  ->
                                        fun pos  ->
                                          fun str'  ->
                                            fun pos'  ->
                                              ((locate str pos str' pos'), x))
                                   (typexpr_lvl (next_type_prio Arr)))
                                (Earley.sequence arrow_re (typexpr_lvl Arr)
                                   (fun _default_0  ->
                                      fun te'  ->
                                        fun te  ->
                                          let (_loc_te,te) = te in
                                          fun ln  ->
                                            fun __loc__start__buf  ->
                                              fun __loc__start__pos  ->
                                                fun __loc__end__buf  ->
                                                  fun __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    loc_typ _loc
                                                      (Ptyp_arrow
                                                         (ln,
                                                           (mkoption _loc_te
                                                              te), te'))))))
                          :: y
                        else y in
                      if lvl = AtomType
                      then
                        (Earley.fsequence (Earley.char '(' '(')
                           (Earley.sequence typexpr (Earley.char ')' ')')
                              (fun te  -> fun _  -> fun _  -> te)))
                        :: y
                      else y in
                    if lvl = AtomType
                    then
                      (Earley.fsequence_position (Earley.char '(' '(')
                         (Earley.fsequence module_kw
                            (Earley.sequence package_type
                               (Earley.char ')' ')')
                               (fun pt  ->
                                  fun _  ->
                                    fun _default_0  ->
                                      fun _  ->
                                        fun __loc__start__buf  ->
                                          fun __loc__start__pos  ->
                                            fun __loc__end__buf  ->
                                              fun __loc__end__pos  ->
                                                let _loc =
                                                  locate __loc__start__buf
                                                    __loc__start__pos
                                                    __loc__end__buf
                                                    __loc__end__pos in
                                                loc_typ _loc pt))))
                      :: y
                    else y in
                  if lvl = AtomType
                  then
                    (Earley.apply_position
                       (fun _default_0  ->
                          fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  loc_typ _loc Ptyp_any) joker_kw)
                    :: y
                  else y in
                if lvl = AtomType
                then
                  (Earley.sequence_position (Earley.string "'" "'") ident
                     (fun _  ->
                        fun id  ->
                          fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  loc_typ _loc (Ptyp_var id)))
                  :: y
                else y in
              if lvl < AtomType
              then (typexpr_lvl (next_type_prio lvl)) :: y
              else y)))
    let type_param = Earley.declare_grammar "type_param"
    let _ =
      Earley.set_grammar type_param
        (Earley.alternatives
           [Earley.fsequence opt_variance
              (Earley.sequence (Earley.char '\'' '\'')
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    ident)
                 (fun _  ->
                    fun id  ->
                      let (_loc_id,id) = id in
                      fun var  -> ((Some (id_loc id _loc_id)), var)));
           Earley.sequence opt_variance (Earley.char '_' '_')
             (fun var  -> fun _  -> (None, var))])
    let type_params = Earley.declare_grammar "type_params"
    let _ =
      Earley.set_grammar type_params
        (Earley.alternatives
           [Earley.apply (fun tp  -> [tp]) type_param;
           Earley.fsequence (Earley.string "(" "(")
             (Earley.fsequence type_param
                (Earley.sequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            (Earley.sequence (Earley.string "," ",")
                               type_param (fun _  -> fun tp  -> tp)))))
                   (Earley.string ")" ")")
                   (fun tps  -> fun _  -> fun tp  -> fun _  -> tp :: tps)))])
    let type_equation = Earley.declare_grammar "type_equation"
    let _ =
      Earley.set_grammar type_equation
        (Earley.fsequence (Earley.char '=' '=')
           (Earley.sequence private_flag typexpr
              (fun p  -> fun te  -> fun _  -> (p, te))))
    let type_constraint = Earley.declare_grammar "type_constraint"
    let _ =
      Earley.set_grammar type_constraint
        (Earley.fsequence_position constraint_kw
           (Earley.fsequence (Earley.string "'" "'")
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    ident)
                 (Earley.sequence (Earley.char '=' '=') typexpr
                    (fun _  ->
                       fun te  ->
                         fun id  ->
                           let (_loc_id,id) = id in
                           fun _  ->
                             fun _default_0  ->
                               fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       ((loc_typ _loc_id (Ptyp_var id)), te,
                                         _loc))))))
    let constr_name2 = Earley.declare_grammar "constr_name2"
    let _ =
      Earley.set_grammar constr_name2
        (Earley.alternatives
           [constr_name;
           Earley.sequence (Earley.string "(" "(") (Earley.string ")" ")")
             (fun _  -> fun _  -> "()")])
    let constr_decl = Earley.declare_grammar "constr_decl"
    let _ =
      Earley.set_grammar constr_decl
        (Earley.sequence_position
           (Earley.apply_position
              (fun x  ->
                 fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> ((locate str pos str' pos'), x))
              constr_name2)
           (Earley.alternatives
              [Earley.apply
                 (fun te  ->
                    let tes =
                      match te with
                      | None  -> []
                      | Some { ptyp_desc = Ptyp_tuple tes; ptyp_loc = _ } ->
                          tes
                      | Some t -> [t] in
                    (tes, None))
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x)
                       (Earley.sequence of_kw typexpr
                          (fun _  -> fun _default_0  -> _default_0))));
              Earley.fsequence (Earley.char ':' ':')
                (Earley.sequence
                   (Earley.option []
                      (Earley.fsequence
                         (typexpr_lvl (next_type_prio ProdType))
                         (Earley.sequence
                            (Earley.apply List.rev
                               (Earley.fixpoint []
                                  (Earley.apply (fun x  -> fun y  -> x :: y)
                                     (Earley.sequence (Earley.char '*' '*')
                                        (typexpr_lvl
                                           (next_type_prio ProdType))
                                        (fun _  ->
                                           fun _default_0  -> _default_0)))))
                            arrow_re
                            (fun tes  ->
                               fun _default_0  -> fun te  -> te :: tes))))
                   (typexpr_lvl (next_type_prio Arr))
                   (fun ats  -> fun te  -> fun _  -> (ats, (Some te))))])
           (fun cn  ->
              let (_loc_cn,cn) = cn in
              fun ((tes,te) as _default_0)  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        let c = id_loc cn _loc_cn in
                        constructor_declaration
                          ~attributes:(attach_attrib ~local:true _loc [])
                          _loc c tes te))
    let field_decl = Earley.declare_grammar "field_decl"
    let _ =
      Earley.set_grammar field_decl
        (Earley.fsequence_position mutable_flag
           (Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 field_name)
              (Earley.sequence (Earley.string ":" ":") poly_typexpr
                 (fun _  ->
                    fun pte  ->
                      fun fn  ->
                        let (_loc_fn,fn) = fn in
                        fun m  ->
                          fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  label_declaration _loc (id_loc fn _loc_fn)
                                    m pte))))
    let all_constr_decl = Earley.declare_grammar "all_constr_decl"
    let _ =
      Earley.set_grammar all_constr_decl
        (Earley.apply (fun cd  -> [cd]) constr_decl)
    let _ =
      set_grammar constr_decl_list
        (Earley.alternatives
           [Earley.fsequence
              (Earley.option None
                 (Earley.apply (fun x  -> Some x) (Earley.string "|" "|")))
              (Earley.sequence all_constr_decl
                 (Earley.apply List.rev
                    (Earley.fixpoint []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          (Earley.sequence (Earley.string "|" "|")
                             all_constr_decl (fun _  -> fun cd  -> cd)))))
                 (fun cd  ->
                    fun cds  -> fun _default_0  -> List.flatten (cd :: cds)));
           Earley.apply (fun _  -> []) (Earley.empty ())])
    let field_decl_aux = Earley.declare_grammar "field_decl_aux"
    let _ =
      Earley.set_grammar field_decl_aux
        (Earley.alternatives
           [Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence field_decl_aux
             (Earley.sequence field_decl semi_col
                (fun fd  -> fun _default_0  -> fun fs  -> fd :: fs))])
    let _ =
      set_grammar field_decl_list
        (Earley.alternatives
           [Earley.apply (fun fs  -> List.rev fs) field_decl_aux;
           Earley.sequence field_decl_aux field_decl
             (fun fs  -> fun fd  -> List.rev (fd :: fs))])
    let type_representation = Earley.declare_grammar "type_representation"
    let _ =
      Earley.set_grammar type_representation
        (Earley.alternatives
           [Earley.fsequence (Earley.string "{" "{")
              (Earley.sequence field_decl_list (Earley.string "}" "}")
                 (fun fds  -> fun _  -> fun _  -> Ptype_record fds));
           Earley.apply
             (fun cds  -> if cds = [] then give_up (); Ptype_variant cds)
             constr_decl_list])
    let type_information = Earley.declare_grammar "type_information"
    let _ =
      Earley.set_grammar type_information
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x) type_equation))
           (Earley.sequence
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.fsequence (Earley.char '=' '=')
                       (Earley.sequence private_flag type_representation
                          (fun pri  -> fun tr  -> fun _  -> (pri, tr))))))
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       type_constraint)))
              (fun ptr  ->
                 fun cstrs  ->
                   fun te  ->
                     let (pri,tkind) =
                       match ptr with
                       | None  -> (Public, Ptype_abstract)
                       | Some c -> c in
                     (pri, te, tkind, cstrs))))
    let typedef_gen attach constr filter =
      Earley.fsequence_position (Earley.option [] type_params)
        (Earley.sequence
           (Earley.apply_position
              (fun x  ->
                 fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> ((locate str pos str' pos'), x)) constr)
           type_information
           (fun tcn  ->
              let (_loc_tcn,tcn) = tcn in
              fun ti  ->
                fun tps  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          fun prev_loc  ->
                            let _loc =
                              match (prev_loc : Location.t option) with
                              | None  -> _loc
                              | Some l -> merge2 l _loc in
                            let (pri,te,tkind,cstrs) = ti in
                            let (pri,te) =
                              match te with
                              | None  -> (pri, None)
                              | Some (Private ,te) ->
                                  (if pri = Private then give_up ();
                                   (Private, (Some te)))
                              | Some (_,te) -> (pri, (Some te)) in
                            ((id_loc tcn _loc_tcn),
                              (type_declaration
                                 ~attributes:(if attach
                                              then attach_attrib _loc []
                                              else []) _loc
                                 (id_loc (filter tcn) _loc_tcn) tps cstrs
                                 tkind pri te))))
    let typedef =
      apply (fun f  -> f None)
        (typedef_gen true typeconstr_name (fun x  -> x))
    let typedef_in_constraint = typedef_gen false typeconstr Longident.last
    let type_definition = Earley.declare_grammar "type_definition"
    let _ =
      Earley.set_grammar type_definition
        (Earley.fsequence type_kw
           (Earley.sequence typedef
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.sequence and_kw typedef
                          (fun _default_0  -> fun td  -> td)))))
              (fun td  -> fun tds  -> fun _default_0  -> td :: tds)))
    let exception_declaration =
      Earley.declare_grammar "exception_declaration"
    let _ =
      Earley.set_grammar exception_declaration
        (Earley.fsequence_position exception_kw
           (Earley.sequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 constr_name)
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.sequence of_kw typexpr
                       (fun _  -> fun _default_0  -> _default_0))))
              (fun cn  ->
                 let (_loc_cn,cn) = cn in
                 fun te  ->
                   fun _default_0  ->
                     fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos in
                             let tes =
                               match te with
                               | None  -> []
                               | Some
                                   { ptyp_desc = Ptyp_tuple tes; ptyp_loc = _
                                     }
                                   -> tes
                               | Some t -> [t] in
                             ((id_loc cn _loc_cn), tes, _loc))))
    let exception_definition = Earley.declare_grammar "exception_definition"
    let _ =
      Earley.set_grammar exception_definition
        (Earley.alternatives
           [Earley.fsequence_position exception_kw
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    constr_name)
                 (Earley.sequence (Earley.char '=' '=')
                    (Earley.apply_position
                       (fun x  ->
                          fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  -> ((locate str pos str' pos'), x))
                       constr)
                    (fun _  ->
                       fun c  ->
                         let (_loc_c,c) = c in
                         fun cn  ->
                           let (_loc_cn,cn) = cn in
                           fun _default_0  ->
                             fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     (let name = id_loc cn _loc_cn in
                                      let ex = id_loc c _loc_c in
                                      Str.exception_ ~loc:_loc
                                        (Te.rebind
                                           ~loc:(merge2 _loc_cn _loc_c) name
                                           ex)).pstr_desc)));
           Earley.apply_position
             (fun ((name,ed,_loc') as _default_0)  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        (Str.exception_ ~loc:_loc
                           (Te.decl ~loc:_loc ~args:ed name)).pstr_desc)
             exception_declaration])
    let class_field_spec = declare_grammar "class_field_spec"
    let class_body_type = declare_grammar "class_body_type"
    let virt_mut = Earley.declare_grammar "virt_mut"
    let _ =
      Earley.set_grammar virt_mut
        (Earley.alternatives
           [Earley.sequence virtual_flag mutable_flag
              (fun v  -> fun m  -> (v, m));
           Earley.sequence mutable_kw virtual_kw
             (fun _default_1  -> fun _default_0  -> (Virtual, Mutable))])
    let virt_priv = Earley.declare_grammar "virt_priv"
    let _ =
      Earley.set_grammar virt_priv
        (Earley.alternatives
           [Earley.sequence virtual_flag private_flag
              (fun v  -> fun p  -> (v, p));
           Earley.sequence private_kw virtual_kw
             (fun _default_1  -> fun _default_0  -> (Virtual, Private))])
    let _ =
      set_grammar class_field_spec
        (Earley.alternatives
           [Earley.sequence_position inherit_kw class_body_type
              (fun _default_0  ->
                 fun cbt  ->
                   fun __loc__start__buf  ->
                     fun __loc__start__pos  ->
                       fun __loc__end__buf  ->
                         fun __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           pctf_loc _loc (Pctf_inherit cbt));
           Earley.fsequence_position val_kw
             (Earley.fsequence virt_mut
                (Earley.fsequence inst_var_name
                   (Earley.sequence (Earley.string ":" ":") typexpr
                      (fun _  ->
                         fun te  ->
                           fun ivn  ->
                             fun ((vir,mut) as _default_0)  ->
                               fun _default_1  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         pctf_loc _loc
                                           (Pctf_val (ivn, mut, vir, te))))));
           Earley.fsequence_position method_kw
             (Earley.fsequence virt_priv
                (Earley.fsequence method_name
                   (Earley.sequence (Earley.string ":" ":") poly_typexpr
                      (fun _  ->
                         fun te  ->
                           fun mn  ->
                             fun ((v,pri) as _default_0)  ->
                               fun _default_1  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         pctf_loc _loc
                                           (Pctf_method (mn, pri, v, te))))));
           Earley.fsequence_position constraint_kw
             (Earley.fsequence typexpr
                (Earley.sequence (Earley.char '=' '=') typexpr
                   (fun _  ->
                      fun te'  ->
                        fun te  ->
                          fun _default_0  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    pctf_loc _loc (Pctf_constraint (te, te')))))])
    let _ =
      set_grammar class_body_type
        (Earley.alternatives
           [Earley.fsequence_position object_kw
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x)
                          (Earley.fsequence (Earley.string "(" "(")
                             (Earley.sequence typexpr (Earley.string ")" ")")
                                (fun te  -> fun _  -> fun _  -> te))))))
                 (Earley.sequence
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             class_field_spec))) end_kw
                    (fun cfs  ->
                       fun _default_0  ->
                         fun te  ->
                           let (_loc_te,te) = te in
                           fun _default_1  ->
                             fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     let self =
                                       match te with
                                       | None  -> loc_typ _loc_te Ptyp_any
                                       | Some t -> t in
                                     let sign =
                                       {
                                         pcsig_self = self;
                                         pcsig_fields = cfs
                                       } in
                                     pcty_loc _loc (Pcty_signature sign))));
           Earley.sequence_position
             (Earley.option []
                (Earley.fsequence (Earley.string "[" "[")
                   (Earley.fsequence typexpr
                      (Earley.sequence
                         (Earley.apply List.rev
                            (Earley.fixpoint []
                               (Earley.apply (fun x  -> fun y  -> x :: y)
                                  (Earley.sequence (Earley.string "," ",")
                                     typexpr (fun _  -> fun te  -> te)))))
                         (Earley.string "]" "]")
                         (fun tes  ->
                            fun _  -> fun te  -> fun _  -> te :: tes)))))
             (Earley.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x))
                classtype_path)
             (fun tes  ->
                fun ctp  ->
                  let (_loc_ctp,ctp) = ctp in
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          let ctp = id_loc ctp _loc_ctp in
                          pcty_loc _loc (Pcty_constr (ctp, tes)))])
    let class_type = Earley.declare_grammar "class_type"
    let _ =
      Earley.set_grammar class_type
        (Earley.sequence_position
           (Earley.apply_position
              (fun x  ->
                 fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> ((locate str pos str' pos'), x))
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.fsequence
                          (Earley.option None
                             (Earley.apply (fun x  -> Some x) maybe_opt_label))
                          (Earley.sequence (Earley.string ":" ":") typexpr
                             (fun _  -> fun te  -> fun l  -> (l, te))))))))
           class_body_type
           (fun tes  ->
              let (_loc_tes,tes) = tes in
              fun cbt  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        let app acc (lab,te) =
                          match lab with
                          | None  ->
                              pcty_loc _loc (Pcty_arrow (nolabel, te, acc))
                          | Some l ->
                              pcty_loc _loc
                                (Pcty_arrow
                                   (l,
                                     (if (l.[0]) = '?'
                                      then mkoption _loc_tes te
                                      else te), acc)) in
                        List.fold_left app cbt (List.rev tes)))
    let type_parameters = Earley.declare_grammar "type_parameters"
    let _ =
      Earley.set_grammar type_parameters
        (Earley.sequence type_param
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.sequence (Earley.string "," ",") type_param
                       (fun _  -> fun i2  -> i2)))))
           (fun i1  -> fun l  -> i1 :: l))
    let class_spec = Earley.declare_grammar "class_spec"
    let _ =
      Earley.set_grammar class_spec
        (Earley.fsequence_position virtual_flag
           (Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 (Earley.option []
                    (Earley.fsequence (Earley.string "[" "[")
                       (Earley.sequence type_parameters
                          (Earley.string "]" "]")
                          (fun params  -> fun _  -> fun _  -> params)))))
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    class_name)
                 (Earley.sequence (Earley.string ":" ":") class_type
                    (fun _  ->
                       fun ct  ->
                         fun cn  ->
                           let (_loc_cn,cn) = cn in
                           fun params  ->
                             let (_loc_params,params) = params in
                             fun v  ->
                               fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       class_type_declaration
                                         ~attributes:(attach_attrib _loc [])
                                         _loc_params _loc (id_loc cn _loc_cn)
                                         params v ct)))))
    let class_specification = Earley.declare_grammar "class_specification"
    let _ =
      Earley.set_grammar class_specification
        (Earley.sequence class_spec
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.sequence and_kw class_spec
                       (fun _  -> fun _default_0  -> _default_0)))))
           (fun cs  -> fun css  -> cs :: css))
    let classtype_def = Earley.declare_grammar "classtype_def"
    let _ =
      Earley.set_grammar classtype_def
        (Earley.fsequence_position virtual_flag
           (Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 (Earley.option []
                    (Earley.fsequence (Earley.string "[" "[")
                       (Earley.sequence type_parameters
                          (Earley.string "]" "]")
                          (fun tp  -> fun _  -> fun _  -> tp)))))
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    class_name)
                 (Earley.sequence (Earley.char '=' '=') class_body_type
                    (fun _  ->
                       fun cbt  ->
                         fun cn  ->
                           let (_loc_cn,cn) = cn in
                           fun params  ->
                             let (_loc_params,params) = params in
                             fun v  ->
                               fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       class_type_declaration
                                         ~attributes:(attach_attrib _loc [])
                                         _loc_params _loc (id_loc cn _loc_cn)
                                         params v cbt)))))
    let classtype_definition = Earley.declare_grammar "classtype_definition"
    let _ =
      Earley.set_grammar classtype_definition
        (Earley.fsequence type_kw
           (Earley.sequence classtype_def
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.sequence and_kw classtype_def
                          (fun _  -> fun _default_0  -> _default_0)))))
              (fun cd  -> fun cds  -> fun _default_0  -> cd :: cds)))
    let integer_litteral = Earley.declare_grammar "integer_litteral"
    let _ =
      Earley.set_grammar integer_litteral
        (Earley.apply
           (fun ((s,co) as _default_0)  ->
              match co with
              | None  -> const_int (int_of_string s)
              | Some 'l' -> const_int32 (Int32.of_string s)
              | Some 'L' -> const_int64 (Int64.of_string s)
              | Some 'n' -> const_nativeint (Nativeint.of_string s)
              | Some _ -> Earley.give_up ()) int_litteral)
    let constant = Earley.declare_grammar "constant"
    let _ =
      Earley.set_grammar constant
        (Earley.alternatives
           [Earley.apply (fun f  -> const_float f) float_litteral;
           Earley.apply (fun c  -> const_char c) char_litteral;
           Earley.apply (fun s  -> const_string s) string_litteral;
           Earley.apply (fun s  -> const_string s) regexp_litteral;
           integer_litteral])
    let neg_constant = Earley.declare_grammar "neg_constant"
    let _ =
      Earley.set_grammar neg_constant
        (Earley.alternatives
           [Earley.sequence
              (Earley.alternatives
                 [Earley.apply (fun _  -> ()) (Earley.char '-' '-');
                 Earley.apply (fun _  -> ()) (Earley.string "-." "-.")])
              float_litteral
              (fun _default_0  -> fun f  -> const_float ("-" ^ f));
           Earley.sequence (Earley.char '-' '-') integer_litteral
             (fun _  ->
                fun i  ->
                  match i with
                  | Const_int i -> const_int (- i)
                  | Const_int32 i -> const_int32 (Int32.neg i)
                  | Const_int64 i -> const_int64 (Int64.neg i)
                  | Const_nativeint i -> const_nativeint (Nativeint.neg i)
                  | _ -> assert false)])
    let (extra_patterns_grammar,extra_patterns_grammar__set__grammar) =
      Earley.grammar_family "extra_patterns_grammar"
    let _ =
      extra_patterns_grammar__set__grammar
        (fun lvl  -> alternatives (List.map (fun g  -> g lvl) extra_patterns))
    let _ =
      set_pattern_lvl
        (fun (as_ok,lvl)  ->
           Earley.alternatives ((extra_patterns_grammar (as_ok, lvl)) ::
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
                                                                 let y =
                                                                   let y = [] in
                                                                   if
                                                                    lvl =
                                                                    ConsPat
                                                                   then
                                                                    (Earley.fsequence_position
                                                                    (pattern_lvl
                                                                    (true,
                                                                    (next_pat_prio
                                                                    ConsPat)))
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (Earley.string
                                                                    "::" "::"))
                                                                    (pattern_lvl
                                                                    (false,
                                                                    ConsPat))
                                                                    (fun c 
                                                                    ->
                                                                    let 
                                                                    (_loc_c,c)
                                                                    = c in
                                                                    fun p' 
                                                                    ->
                                                                    fun p  ->
                                                                    fun
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
                                                                   lvl =
                                                                    TupPat
                                                                 then
                                                                   (Earley.sequence_position
                                                                    (Earley.apply
                                                                    List.rev
                                                                    (Earley.fixpoint1
                                                                    []
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                    (Earley.sequence
                                                                    (pattern_lvl
                                                                    (true,
                                                                    (next_pat_prio
                                                                    TupPat)))
                                                                    (Earley.char
                                                                    ',' ',')
                                                                    (fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    _default_0)))))
                                                                    (pattern_lvl
                                                                    (false,
                                                                    (next_pat_prio
                                                                    TupPat)))
                                                                    (fun ps 
                                                                    ->
                                                                    fun p  ->
                                                                    fun
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
                                                                    loc_pat
                                                                    _loc
                                                                    (Ppat_tuple
                                                                    (ps @ [p]))))
                                                                   :: y
                                                                 else y in
                                                               if
                                                                 lvl = AltPat
                                                               then
                                                                 (Earley.fsequence_position
                                                                    (
                                                                    pattern_lvl
                                                                    (true,
                                                                    AltPat))
                                                                    (
                                                                    Earley.sequence
                                                                    (Earley.char
                                                                    '|' '|')
                                                                    (pattern_lvl
                                                                    (false,
                                                                    (next_pat_prio
                                                                    AltPat)))
                                                                    (fun _ 
                                                                    ->
                                                                    fun p' 
                                                                    ->
                                                                    fun p  ->
                                                                    fun
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
                                                                    loc_pat
                                                                    _loc
                                                                    (Ppat_or
                                                                    (p, p')))))
                                                                 :: y
                                                               else y in
                                                             if lvl = AtomPat
                                                             then
                                                               (Earley.fsequence_position
                                                                  (Earley.ignore_next_blank
                                                                    (Earley.char
                                                                    '$' '$'))
                                                                  (Earley.fsequence
                                                                    (Earley.option
                                                                    "pat"
                                                                    (Earley.sequence
                                                                    (Earley.ignore_next_blank
                                                                    (EarleyStr.regexp
                                                                    ~name:"[a-z]+"
                                                                    "[a-z]+"
                                                                    (fun
                                                                    groupe 
                                                                    ->
                                                                    groupe 0)))
                                                                    (Earley.char
                                                                    ':' ':')
                                                                    (fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    _default_0)))
                                                                    (Earley.sequence
                                                                    (Earley.ignore_next_blank
                                                                    expression)
                                                                    (Earley.char
                                                                    '$' '$')
                                                                    (fun e 
                                                                    ->
                                                                    fun _  ->
                                                                    fun aq 
                                                                    ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    _loc _loc));
                                                                    ((parsetree
                                                                    "ppat_attributes"),
                                                                    (quote_attributes
                                                                    e_loc
                                                                    _loc []))] in
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
                                                                    () in
                                                                    Quote.ppat_antiquotation
                                                                    _loc f))))
                                                               :: y
                                                             else y in
                                                           if lvl = AtomPat
                                                           then
                                                             (Earley.sequence
                                                                (Earley.ignore_next_blank
                                                                   (Earley.char
                                                                    '$' '$'))
                                                                uident
                                                                (fun _  ->
                                                                   fun c  ->
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
                                                                    | 
                                                                    Not_found
                                                                     ->
                                                                    give_up
                                                                    ()))
                                                             :: y
                                                           else y in
                                                         if lvl = AtomPat
                                                         then
                                                           (Earley.fsequence_position
                                                              (Earley.char
                                                                 '(' '(')
                                                              (Earley.fsequence
                                                                 module_kw
                                                                 (Earley.fsequence
                                                                    (
                                                                    Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_name)
                                                                    (
                                                                    Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (Earley.option
                                                                    None
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Earley.sequence
                                                                    (Earley.string
                                                                    ":" ":")
                                                                    package_type
                                                                    (fun _ 
                                                                    ->
                                                                    fun pt 
                                                                    -> pt)))))
                                                                    (Earley.char
                                                                    ')' ')')
                                                                    (fun pt 
                                                                    ->
                                                                    let 
                                                                    (_loc_pt,pt)
                                                                    = pt in
                                                                    fun _  ->
                                                                    fun mn 
                                                                    ->
                                                                    let 
                                                                    (_loc_mn,mn)
                                                                    = mn in
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    fun
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
                                                         (Earley.sequence_position
                                                            begin_kw end_kw
                                                            (fun _default_1 
                                                               ->
                                                               fun _default_0
                                                                  ->
                                                                 fun
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
                                                                    let unt =
                                                                    id_loc
                                                                    (Lident
                                                                    "()")
                                                                    _loc in
                                                                    loc_pat
                                                                    _loc
                                                                    (ppat_construct
                                                                    (unt,
                                                                    None))))
                                                         :: y
                                                       else y in
                                                     if lvl = AtomPat
                                                     then
                                                       (Earley.sequence_position
                                                          (Earley.string "("
                                                             "(")
                                                          (Earley.string ")"
                                                             ")")
                                                          (fun _  ->
                                                             fun _  ->
                                                               fun
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
                                                                    let unt =
                                                                    id_loc
                                                                    (Lident
                                                                    "()")
                                                                    _loc in
                                                                    loc_pat
                                                                    _loc
                                                                    (ppat_construct
                                                                    (unt,
                                                                    None))))
                                                       :: y
                                                     else y in
                                                   if lvl = AtomPat
                                                   then
                                                     (Earley.sequence_position
                                                        (Earley.string "[|"
                                                           "[|")
                                                        (Earley.string "|]"
                                                           "|]")
                                                        (fun _  ->
                                                           fun _  ->
                                                             fun
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
                                                                    loc_pat
                                                                    _loc
                                                                    (Ppat_array
                                                                    [])))
                                                     :: y
                                                   else y in
                                                 if lvl = AtomPat
                                                 then
                                                   (Earley.fsequence_position
                                                      (Earley.string "[|"
                                                         "[|")
                                                      (Earley.fsequence
                                                         pattern
                                                         (Earley.fsequence
                                                            (Earley.apply
                                                               List.rev
                                                               (Earley.fixpoint
                                                                  []
                                                                  (Earley.apply
                                                                    (fun x 
                                                                    ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                    (Earley.sequence
                                                                    semi_col
                                                                    pattern
                                                                    (fun
                                                                    _default_0
                                                                     ->
                                                                    fun p  ->
                                                                    p)))))
                                                            (Earley.sequence
                                                               (Earley.option
                                                                  None
                                                                  (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    semi_col))
                                                               (Earley.string
                                                                  "|]" "|]")
                                                               (fun
                                                                  _default_0 
                                                                  ->
                                                                  fun _  ->
                                                                    fun ps 
                                                                    ->
                                                                    fun p  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    loc_pat
                                                                    _loc
                                                                    (Ppat_array
                                                                    (p :: ps)))))))
                                                   :: y
                                                 else y in
                                               if lvl = AtomPat
                                               then
                                                 (Earley.sequence_position
                                                    (Earley.string "[" "[")
                                                    (Earley.string "]" "]")
                                                    (fun _  ->
                                                       fun _  ->
                                                         fun
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
                                                                 let nil =
                                                                   id_loc
                                                                    (Lident
                                                                    "[]")
                                                                    _loc in
                                                                 loc_pat _loc
                                                                   (ppat_construct
                                                                    (nil,
                                                                    None))))
                                                 :: y
                                               else y in
                                             if lvl = AtomPat
                                             then
                                               (Earley.fsequence_position
                                                  (Earley.string "[" "[")
                                                  (Earley.fsequence pattern
                                                     (Earley.fsequence
                                                        (Earley.apply
                                                           List.rev
                                                           (Earley.fixpoint
                                                              []
                                                              (Earley.apply
                                                                 (fun x  ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                 (Earley.sequence
                                                                    semi_col
                                                                    pattern
                                                                    (
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    fun p  ->
                                                                    p)))))
                                                        (Earley.sequence
                                                           (Earley.option
                                                              None
                                                              (Earley.apply
                                                                 (fun x  ->
                                                                    Some x)
                                                                 semi_col))
                                                           (Earley.string "]"
                                                              "]")
                                                           (fun _default_0 
                                                              ->
                                                              fun _  ->
                                                                fun ps  ->
                                                                  fun p  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    pat_list
                                                                    _loc (p
                                                                    :: ps))))))
                                               :: y
                                             else y in
                                           if lvl = AtomPat
                                           then
                                             (Earley.fsequence_position
                                                (Earley.char '{' '{')
                                                (Earley.fsequence
                                                   (Earley.apply_position
                                                      (fun x  ->
                                                         fun str  ->
                                                           fun pos  ->
                                                             fun str'  ->
                                                               fun pos'  ->
                                                                 ((locate str
                                                                    pos str'
                                                                    pos'), x))
                                                      field)
                                                   (Earley.fsequence
                                                      (Earley.option None
                                                         (Earley.apply
                                                            (fun x  -> Some x)
                                                            (Earley.sequence
                                                               (Earley.char
                                                                  '=' '=')
                                                               pattern
                                                               (fun _  ->
                                                                  fun p  -> p))))
                                                      (Earley.fsequence
                                                         (Earley.apply
                                                            List.rev
                                                            (Earley.fixpoint
                                                               []
                                                               (Earley.apply
                                                                  (fun x  ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                  (Earley.fsequence
                                                                    semi_col
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x)) field)
                                                                    (Earley.option
                                                                    None
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Earley.sequence
                                                                    (Earley.char
                                                                    '=' '=')
                                                                    pattern
                                                                    (fun _ 
                                                                    ->
                                                                    fun p  ->
                                                                    p))))
                                                                    (fun f 
                                                                    ->
                                                                    let 
                                                                    (_loc_f,f)
                                                                    = f in
                                                                    fun p  ->
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    ((id_loc
                                                                    f _loc_f),
                                                                    p)))))))
                                                         (Earley.fsequence
                                                            (Earley.option
                                                               None
                                                               (Earley.apply
                                                                  (fun x  ->
                                                                    Some x)
                                                                  (Earley.sequence
                                                                    semi_col
                                                                    joker_kw
                                                                    (fun
                                                                    _default_1
                                                                     ->
                                                                    fun
                                                                    _default_0
                                                                     -> ()))))
                                                            (Earley.sequence
                                                               (Earley.option
                                                                  None
                                                                  (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    semi_col))
                                                               (Earley.char
                                                                  '}' '}')
                                                               (fun
                                                                  _default_0 
                                                                  ->
                                                                  fun _  ->
                                                                    fun clsd 
                                                                    ->
                                                                    fun fps 
                                                                    ->
                                                                    fun p  ->
                                                                    fun f  ->
                                                                    let 
                                                                    (_loc_f,f)
                                                                    = f in
                                                                    fun s  ->
                                                                    fun
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
                                                                    () in
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
                                                                    (Ppat_record
                                                                    (all, cl)))))))))
                                             :: y
                                           else y in
                                         if lvl = AtomPat
                                         then
                                           (Earley.sequence_position
                                              (Earley.char '#' '#')
                                              (Earley.apply_position
                                                 (fun x  ->
                                                    fun str  ->
                                                      fun pos  ->
                                                        fun str'  ->
                                                          fun pos'  ->
                                                            ((locate str pos
                                                                str' pos'),
                                                              x)) typeconstr)
                                              (fun s  ->
                                                 fun t  ->
                                                   let (_loc_t,t) = t in
                                                   fun __loc__start__buf  ->
                                                     fun __loc__start__pos 
                                                       ->
                                                       fun __loc__end__buf 
                                                         ->
                                                         fun __loc__end__pos 
                                                           ->
                                                           let _loc =
                                                             locate
                                                               __loc__start__buf
                                                               __loc__start__pos
                                                               __loc__end__buf
                                                               __loc__end__pos in
                                                           loc_pat _loc
                                                             (Ppat_type
                                                                (id_loc t
                                                                   _loc_t))))
                                           :: y
                                         else y in
                                       if lvl = AtomPat
                                       then
                                         (Earley.apply_position
                                            (fun c  ->
                                               fun __loc__start__buf  ->
                                                 fun __loc__start__pos  ->
                                                   fun __loc__end__buf  ->
                                                     fun __loc__end__pos  ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       loc_pat _loc
                                                         (Ppat_variant
                                                            (c, None)))
                                            tag_name)
                                         :: y
                                       else y in
                                     if lvl = ConstrPat
                                     then
                                       (Earley.sequence_position tag_name
                                          (pattern_lvl (false, ConstrPat))
                                          (fun c  ->
                                             fun p  ->
                                               fun __loc__start__buf  ->
                                                 fun __loc__start__pos  ->
                                                   fun __loc__end__buf  ->
                                                     fun __loc__end__pos  ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       loc_pat _loc
                                                         (Ppat_variant
                                                            (c, (Some p)))))
                                       :: y
                                     else y in
                                   if lvl = AtomPat
                                   then
                                     (Earley.apply_position
                                        (fun b  ->
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let fls =
                                                     id_loc (Lident b) _loc in
                                                   loc_pat _loc
                                                     (ppat_construct
                                                        (fls, None)))
                                        bool_lit)
                                     :: y
                                   else y in
                                 if lvl = AtomPat
                                 then
                                   (Earley.apply_position
                                      (fun c  ->
                                         let (_loc_c,c) = c in
                                         fun __loc__start__buf  ->
                                           fun __loc__start__pos  ->
                                             fun __loc__end__buf  ->
                                               fun __loc__end__pos  ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 let ast =
                                                   ppat_construct
                                                     ((id_loc c _loc_c),
                                                       None) in
                                                 loc_pat _loc ast)
                                      (Earley.apply_position
                                         (fun x  ->
                                            fun str  ->
                                              fun pos  ->
                                                fun str'  ->
                                                  fun pos'  ->
                                                    ((locate str pos str'
                                                        pos'), x)) constr))
                                   :: y
                                 else y in
                               if lvl = ConstrPat
                               then
                                 (Earley.sequence_position
                                    (Earley.apply_position
                                       (fun x  ->
                                          fun str  ->
                                            fun pos  ->
                                              fun str'  ->
                                                fun pos'  ->
                                                  ((locate str pos str' pos'),
                                                    x)) constr)
                                    (pattern_lvl (false, ConstrPat))
                                    (fun c  ->
                                       let (_loc_c,c) = c in
                                       fun p  ->
                                         fun __loc__start__buf  ->
                                           fun __loc__start__pos  ->
                                             fun __loc__end__buf  ->
                                               fun __loc__end__pos  ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 let ast =
                                                   ppat_construct
                                                     ((id_loc c _loc_c),
                                                       (Some p)) in
                                                 loc_pat _loc ast))
                                 :: y
                               else y in
                             if lvl = ConstrPat
                             then
                               (Earley.sequence_position exception_kw
                                  (pattern_lvl (false, ConstrPat))
                                  (fun _default_0  ->
                                     fun p  ->
                                       fun __loc__start__buf  ->
                                         fun __loc__start__pos  ->
                                           fun __loc__end__buf  ->
                                             fun __loc__end__pos  ->
                                               let _loc =
                                                 locate __loc__start__buf
                                                   __loc__start__pos
                                                   __loc__end__buf
                                                   __loc__end__pos in
                                               let ast = Ppat_exception p in
                                               loc_pat _loc ast))
                               :: y
                             else y in
                           if lvl = ConstrPat
                           then
                             (Earley.sequence_position lazy_kw
                                (pattern_lvl (false, ConstrPat))
                                (fun _default_0  ->
                                   fun p  ->
                                     fun __loc__start__buf  ->
                                       fun __loc__start__pos  ->
                                         fun __loc__end__buf  ->
                                           fun __loc__end__pos  ->
                                             let _loc =
                                               locate __loc__start__buf
                                                 __loc__start__pos
                                                 __loc__end__buf
                                                 __loc__end__pos in
                                             let ast = Ppat_lazy p in
                                             loc_pat _loc ast))
                             :: y
                           else y in
                         if lvl = AtomPat
                         then
                           (Earley.fsequence_position (Earley.char '(' '(')
                              (Earley.fsequence pattern
                                 (Earley.sequence
                                    (Earley.option None
                                       (Earley.apply (fun x  -> Some x)
                                          (Earley.sequence
                                             (Earley.char ':' ':') typexpr
                                             (fun _  ->
                                                fun _default_0  -> _default_0))))
                                    (Earley.char ')' ')')
                                    (fun ty  ->
                                       fun _  ->
                                         fun p  ->
                                           fun _  ->
                                             fun __loc__start__buf  ->
                                               fun __loc__start__pos  ->
                                                 fun __loc__end__buf  ->
                                                   fun __loc__end__pos  ->
                                                     let _loc =
                                                       locate
                                                         __loc__start__buf
                                                         __loc__start__pos
                                                         __loc__end__buf
                                                         __loc__end__pos in
                                                     let p =
                                                       match ty with
                                                       | None  ->
                                                           loc_pat _loc
                                                             p.ppat_desc
                                                       | Some ty ->
                                                           loc_pat _loc
                                                             (Ppat_constraint
                                                                (p, ty)) in
                                                     p))))
                           :: y
                         else y in
                       if lvl = AtomPat
                       then
                         (Earley.apply_position
                            (fun c  ->
                               fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       loc_pat _loc (Ppat_constant c))
                            (Earley.alternatives [constant; neg_constant]))
                         :: y
                       else y in
                     if lvl = AtomPat
                     then
                       (Earley.fsequence_position char_litteral
                          (Earley.sequence (Earley.string ".." "..")
                             char_litteral
                             (fun _  ->
                                fun c2  ->
                                  fun c1  ->
                                    fun __loc__start__buf  ->
                                      fun __loc__start__pos  ->
                                        fun __loc__end__buf  ->
                                          fun __loc__end__pos  ->
                                            let _loc =
                                              locate __loc__start__buf
                                                __loc__start__pos
                                                __loc__end__buf
                                                __loc__end__pos in
                                            let (ic1,ic2) =
                                              ((Char.code c1),
                                                (Char.code c2)) in
                                            if ic1 > ic2 then assert false;
                                            loc_pat _loc
                                              (Ppat_interval
                                                 ((const_char (Char.chr ic1)),
                                                   (const_char (Char.chr ic2)))))))
                       :: y
                     else y in
                   if lvl = AtomPat
                   then
                     (Earley.apply_position
                        (fun _default_0  ->
                           fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos in
                                   loc_pat _loc Ppat_any) joker_kw)
                     :: y
                   else y in
                 if lvl = AtomPat
                 then
                   (Earley.apply_position
                      (fun vn  ->
                         let (_loc_vn,vn) = vn in
                         fun __loc__start__buf  ->
                           fun __loc__start__pos  ->
                             fun __loc__end__buf  ->
                               fun __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos in
                                 loc_pat _loc (Ppat_var (id_loc vn _loc_vn)))
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         value_name))
                   :: y
                 else y) in
              if as_ok
              then
                (Earley.fsequence_position (pattern_lvl (as_ok, lvl))
                   (Earley.sequence as_kw
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         value_name)
                      (fun _default_0  ->
                         fun vn  ->
                           let (_loc_vn,vn) = vn in
                           fun p  ->
                             fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     loc_pat _loc
                                       (Ppat_alias (p, (id_loc vn _loc_vn))))))
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
    let bigarray_get _loc arr arg =
      let get = if !fast then "unsafe_get" else "get" in
      match untuplify arg with
      | c1::[] ->
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_apply
                 ({
                    Parsetree.pexp_desc =
                      (Parsetree.Pexp_ident
                         {
                           Asttypes.txt =
                             (Longident.Ldot
                                ((Longident.Ldot
                                    ((Longident.Lident "Bigarry"), "Array1")),
                                  get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }, [("", arr); ("", c1)]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
      | c1::c2::[] ->
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_apply
                 ({
                    Parsetree.pexp_desc =
                      (Parsetree.Pexp_ident
                         {
                           Asttypes.txt =
                             (Longident.Ldot
                                ((Longident.Ldot
                                    ((Longident.Lident "Bigarry"), "Array2")),
                                  get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }, [("", arr); ("", c1); ("", c2)]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
      | c1::c2::c3::[] ->
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_apply
                 ({
                    Parsetree.pexp_desc =
                      (Parsetree.Pexp_ident
                         {
                           Asttypes.txt =
                             (Longident.Ldot
                                ((Longident.Ldot
                                    ((Longident.Lident "Bigarry"), "Array3")),
                                  get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }, [("", arr); ("", c1); ("", c2); ("", c3)]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
      | coords ->
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_apply
                 ({
                    Parsetree.pexp_desc =
                      (Parsetree.Pexp_ident
                         {
                           Asttypes.txt =
                             (Longident.Ldot
                                ((Longident.Ldot
                                    ((Longident.Lident "Bigarry"),
                                      "Genarray")), get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }, [("", arr); ("", (Pa_ast.exp_array _loc coords))]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
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
    let constructor = Earley.declare_grammar "constructor"
    let _ =
      Earley.set_grammar constructor
        (Earley.sequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence module_path (Earley.string "." ".")
                    (fun m  -> fun _  -> m))))
           (Earley.alternatives [uident; bool_lit])
           (fun m  ->
              fun id  ->
                match m with | None  -> Lident id | Some m -> Ldot (m, id)))
    let argument = Earley.declare_grammar "argument"
    let _ =
      Earley.set_grammar argument
        (Earley.alternatives
           [Earley.apply_position
              (fun id  ->
                 fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         ((labelled id),
                           (loc_expr _loc
                              (Pexp_ident (id_loc (Lident id) _loc))))) label;
           Earley.sequence ty_label
             (expression_lvl (NoMatch, (next_exp App)))
             (fun id  -> fun e  -> (id, e));
           Earley.apply_position
             (fun id  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        ((optional id),
                          (loc_expr _loc
                             (Pexp_ident (id_loc (Lident id) _loc)))))
             opt_label;
           Earley.sequence ty_opt_label
             (expression_lvl (NoMatch, (next_exp App)))
             (fun id  -> fun e  -> (id, e));
           Earley.apply (fun e  -> (nolabel, e))
             (expression_lvl (NoMatch, (next_exp App)))])
    let _ =
      set_parameter
        (fun allow_new_type  ->
           Earley.alternatives
             ((Earley.apply (fun pat  -> `Arg (nolabel, None, pat))
                 (pattern_lvl (false, AtomPat))) ::
             (Earley.fsequence_position (Earley.char '~' '~')
                (Earley.fsequence (Earley.char '(' '(')
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x)) lident)
                      (Earley.sequence
                         (Earley.option None
                            (Earley.apply (fun x  -> Some x)
                               (Earley.sequence (Earley.string ":" ":")
                                  typexpr (fun _  -> fun t  -> t))))
                         (Earley.string ")" ")")
                         (fun t  ->
                            fun _  ->
                              fun id  ->
                                let (_loc_id,id) = id in
                                fun _  ->
                                  fun _  ->
                                    fun __loc__start__buf  ->
                                      fun __loc__start__pos  ->
                                        fun __loc__end__buf  ->
                                          fun __loc__end__pos  ->
                                            let _loc =
                                              locate __loc__start__buf
                                                __loc__start__pos
                                                __loc__end__buf
                                                __loc__end__pos in
                                            let pat =
                                              loc_pat _loc_id
                                                (Ppat_var (id_loc id _loc_id)) in
                                            let pat =
                                              match t with
                                              | None  -> pat
                                              | Some t ->
                                                  loc_pat _loc
                                                    (Ppat_constraint (pat, t)) in
                                            `Arg ((labelled id), None, pat))))))
             ::
             (Earley.sequence ty_label pattern
                (fun id  -> fun pat  -> `Arg (id, None, pat))) ::
             (Earley.fsequence (Earley.char '~' '~')
                (Earley.sequence
                   (Earley.apply_position
                      (fun x  ->
                         fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  -> ((locate str pos str' pos'), x))
                      ident) no_colon
                   (fun id  ->
                      let (_loc_id,id) = id in
                      fun _default_0  ->
                        fun _  ->
                          `Arg
                            ((labelled id), None,
                              (loc_pat _loc_id (Ppat_var (id_loc id _loc_id)))))))
             ::
             (Earley.fsequence (Earley.char '?' '?')
                (Earley.fsequence (Earley.char '(' '(')
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x)) lident)
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun x  ->
                               fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       ((locate str pos str' pos'), x))
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.sequence (Earley.char ':' ':')
                                     typexpr (fun _  -> fun t  -> t)))))
                         (Earley.sequence
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.sequence (Earley.char '=' '=')
                                     expression (fun _  -> fun e  -> e))))
                            (Earley.char ')' ')')
                            (fun e  ->
                               fun _  ->
                                 fun t  ->
                                   let (_loc_t,t) = t in
                                   fun id  ->
                                     let (_loc_id,id) = id in
                                     fun _  ->
                                       fun _  ->
                                         let pat =
                                           loc_pat _loc_id
                                             (Ppat_var (id_loc id _loc_id)) in
                                         let pat =
                                           match t with
                                           | None  -> pat
                                           | Some t ->
                                               loc_pat
                                                 (merge2 _loc_id _loc_t)
                                                 (Ppat_constraint (pat, t)) in
                                         `Arg ((optional id), e, pat)))))))
             ::
             (Earley.fsequence ty_opt_label
                (Earley.fsequence (Earley.string "(" "(")
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x)) pattern)
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun x  ->
                               fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       ((locate str pos str' pos'), x))
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.sequence (Earley.char ':' ':')
                                     typexpr (fun _  -> fun t  -> t)))))
                         (Earley.sequence
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.sequence (Earley.char '=' '=')
                                     expression (fun _  -> fun e  -> e))))
                            (Earley.char ')' ')')
                            (fun e  ->
                               fun _  ->
                                 fun t  ->
                                   let (_loc_t,t) = t in
                                   fun pat  ->
                                     let (_loc_pat,pat) = pat in
                                     fun _  ->
                                       fun id  ->
                                         let pat =
                                           match t with
                                           | None  -> pat
                                           | Some t ->
                                               loc_pat
                                                 (merge2 _loc_pat _loc_t)
                                                 (Ppat_constraint (pat, t)) in
                                         `Arg (id, e, pat))))))) ::
             (Earley.sequence ty_opt_label pattern
                (fun id  -> fun pat  -> `Arg (id, None, pat))) ::
             (Earley.apply
                (fun id  ->
                   let (_loc_id,id) = id in
                   `Arg
                     ((optional id), None,
                       (loc_pat _loc_id (Ppat_var (id_loc id _loc_id)))))
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   opt_label)) ::
             (let y = [] in
              if allow_new_type
              then
                (Earley.fsequence (Earley.char '(' '(')
                   (Earley.fsequence type_kw
                      (Earley.sequence typeconstr_name (Earley.char ')' ')')
                         (fun name  ->
                            fun _  -> fun _default_0  -> fun _  -> `Type name))))
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
    let right_member = Earley.declare_grammar "right_member"
    let _ =
      Earley.set_grammar right_member
        (Earley.fsequence_position
           (Earley.apply List.rev
              (Earley.fixpoint1 []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.apply
                       (fun lb  -> let (_loc_lb,lb) = lb in (lb, _loc_lb))
                       (Earley.apply_position
                          (fun x  ->
                             fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     ((locate str pos str' pos'), x))
                          (parameter true))))))
           (Earley.fsequence
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.sequence (Earley.char ':' ':') typexpr
                       (fun _  -> fun t  -> t))))
              (Earley.sequence (Earley.char '=' '=') expression
                 (fun _  ->
                    fun e  ->
                      fun ty  ->
                        fun l  ->
                          fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  let e =
                                    match ty with
                                    | None  -> e
                                    | Some ty ->
                                        loc_expr (ghost _loc)
                                          (pexp_constraint (e, ty)) in
                                  apply_params ~gh:true l e))))
    let eright_member = Earley.declare_grammar "eright_member"
    let _ =
      Earley.set_grammar eright_member
        (Earley.fsequence_position
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.sequence (Earley.char ':' ':') typexpr
                    (fun _  -> fun t  -> t))))
           (Earley.sequence (Earley.char '=' '=') expression
              (fun _  ->
                 fun e  ->
                   fun ty  ->
                     fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos in
                             let e =
                               match ty with
                               | None  -> e
                               | Some ty ->
                                   loc_expr (ghost _loc)
                                     (pexp_constraint (e, ty)) in
                             e)))
    let _ =
      set_grammar let_binding
        (Earley.alternatives
           [Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 pattern)
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    eright_member)
                 (Earley.sequence post_item_attributes
                    (Earley.option []
                       (Earley.sequence and_kw let_binding
                          (fun _  -> fun _default_0  -> _default_0)))
                    (fun a  ->
                       fun l  ->
                         fun e  ->
                           let (_loc_e,e) = e in
                           fun pat  ->
                             let (_loc_pat,pat) = pat in
                             let loc = merge2 _loc_pat _loc_e in
                             (value_binding ~attributes:(attach_attrib loc a)
                                loc pat e)
                               :: l)));
           Earley.fsequence
             (Earley.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x))
                value_name)
             (Earley.fsequence
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   right_member)
                (Earley.sequence post_item_attributes
                   (Earley.option []
                      (Earley.sequence and_kw let_binding
                         (fun _  -> fun _default_0  -> _default_0)))
                   (fun a  ->
                      fun l  ->
                        fun e  ->
                          let (_loc_e,e) = e in
                          fun vn  ->
                            let (_loc_vn,vn) = vn in
                            let loc = merge2 _loc_vn _loc_e in
                            let pat = pat_ident _loc_vn vn in
                            (value_binding ~attributes:(attach_attrib loc a)
                               loc pat e)
                              :: l)));
           Earley.fsequence_position
             (Earley.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x))
                value_name)
             (Earley.fsequence (Earley.char ':' ':')
                (Earley.fsequence only_poly_typexpr
                   (Earley.fsequence (Earley.char '=' '=')
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun x  ->
                               fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       ((locate str pos str' pos'), x))
                            expression)
                         (Earley.sequence post_item_attributes
                            (Earley.option []
                               (Earley.sequence and_kw let_binding
                                  (fun _  -> fun _default_0  -> _default_0)))
                            (fun a  ->
                               fun l  ->
                                 fun e  ->
                                   let (_loc_e,e) = e in
                                   fun _  ->
                                     fun ty  ->
                                       fun _  ->
                                         fun vn  ->
                                           let (_loc_vn,vn) = vn in
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let pat =
                                                     loc_pat _loc
                                                       (Ppat_constraint
                                                          ((loc_pat _loc
                                                              (Ppat_var
                                                                 (id_loc vn
                                                                    _loc_vn))),
                                                            ty)) in
                                                   let loc =
                                                     merge2 _loc_vn _loc_e in
                                                   (value_binding
                                                      ~attributes:(attach_attrib
                                                                    loc a)
                                                      loc pat e)
                                                     :: l))))));
           Earley.fsequence_position
             (Earley.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x))
                value_name)
             (Earley.fsequence (Earley.char ':' ':')
                (Earley.fsequence poly_syntax_typexpr
                   (Earley.fsequence (Earley.char '=' '=')
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun x  ->
                               fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       ((locate str pos str' pos'), x))
                            expression)
                         (Earley.sequence post_item_attributes
                            (Earley.option []
                               (Earley.sequence and_kw let_binding
                                  (fun _  -> fun _default_0  -> _default_0)))
                            (fun a  ->
                               fun l  ->
                                 fun e  ->
                                   let (_loc_e,e) = e in
                                   fun _  ->
                                     fun ((ids,ty) as _default_0)  ->
                                       fun _  ->
                                         fun vn  ->
                                           let (_loc_vn,vn) = vn in
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let (e,ty) =
                                                     wrap_type_annotation
                                                       _loc ids ty e in
                                                   let pat =
                                                     loc_pat _loc
                                                       (Ppat_constraint
                                                          ((loc_pat _loc
                                                              (Ppat_var
                                                                 (id_loc vn
                                                                    _loc_vn))),
                                                            ty)) in
                                                   let loc =
                                                     merge2 _loc_vn _loc_e in
                                                   (value_binding
                                                      ~attributes:(attach_attrib
                                                                    loc a)
                                                      loc pat e)
                                                     :: l))))))])
    let (match_case,match_case__set__grammar) =
      Earley.grammar_family "match_case"
    let _ =
      match_case__set__grammar
        (fun c  ->
           Earley.fsequence pattern
             (Earley.fsequence
                (Earley.option None
                   (Earley.apply (fun x  -> Some x)
                      (Earley.sequence when_kw expression
                         (fun _  -> fun _default_0  -> _default_0))))
                (Earley.sequence arrow_re (expression_lvl c)
                   (fun _default_0  ->
                      fun e  -> fun w  -> fun pat  -> make_case pat e w))))
    let _ =
      set_grammar match_cases
        (Earley.alternatives
           [Earley.fsequence
              (Earley.option None
                 (Earley.apply (fun x  -> Some x) (Earley.char '|' '|')))
              (Earley.fsequence
                 (Earley.apply List.rev
                    (Earley.fixpoint []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          (Earley.sequence (match_case (Let, Seq))
                             (Earley.char '|' '|')
                             (fun _default_0  -> fun _  -> _default_0)))))
                 (Earley.sequence (match_case (Match, Seq)) no_semi
                    (fun x  ->
                       fun _default_0  ->
                         fun l  -> fun _default_1  -> l @ [x])));
           Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence_position
             (Earley.ignore_next_blank (Earley.char '$' '$'))
             (Earley.fsequence
                (Earley.option "cases"
                   (Earley.sequence (Earley.string "cases" "cases")
                      (Earley.string ":" ":") (fun c  -> fun _  -> c)))
                (Earley.sequence (Earley.ignore_next_blank expression)
                   (Earley.char '$' '$')
                   (fun e  ->
                      fun _  ->
                        fun aq  ->
                          fun _  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    let open Quote in
                                      let generic_antiquote e =
                                        function
                                        | Quote_loc  -> e
                                        | _ ->
                                            failwith
                                              "invalid antiquotation type" in
                                      let f =
                                        match aq with
                                        | "cases" -> generic_antiquote e
                                        | _ -> give_up () in
                                      make_list_antiquotation _loc Quote_loc
                                        f)))])
    let type_coercion = Earley.declare_grammar "type_coercion"
    let _ =
      Earley.set_grammar type_coercion
        (Earley.alternatives
           [Earley.fsequence (Earley.string ":" ":")
              (Earley.sequence typexpr
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x)
                       (Earley.sequence (Earley.string ":>" ":>") typexpr
                          (fun _  -> fun t'  -> t'))))
                 (fun t  -> fun t'  -> fun _  -> ((Some t), t')));
           Earley.sequence (Earley.string ":>" ":>") typexpr
             (fun _  -> fun t'  -> (None, (Some t')))])
    let expression_list = Earley.declare_grammar "expression_list"
    let _ =
      Earley.set_grammar expression_list
        (Earley.alternatives
           [Earley.fsequence
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.sequence
                          (Earley.apply_position
                             (fun x  ->
                                fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        ((locate str pos str' pos'), x))
                             (expression_lvl (LetRight, (next_exp Seq))))
                          semi_col
                          (fun e  ->
                             let (_loc_e,e) = e in fun _  -> (e, _loc_e))))))
              (Earley.sequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    (expression_lvl (Match, (next_exp Seq))))
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x) semi_col))
                 (fun e  ->
                    let (_loc_e,e) = e in
                    fun _default_0  -> fun l  -> l @ [(e, _loc_e)]));
           Earley.apply (fun _  -> []) (Earley.empty ())])
    let record_item = Earley.declare_grammar "record_item"
    let _ =
      Earley.set_grammar record_item
        (Earley.alternatives
           [Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x)) field)
              (Earley.sequence (Earley.char '=' '=')
                 (expression_lvl (LetRight, (next_exp Seq)))
                 (fun _  ->
                    fun e  ->
                      fun f  -> let (_loc_f,f) = f in ((id_loc f _loc_f), e)));
           Earley.apply
             (fun f  ->
                let (_loc_f,f) = f in
                let id = id_loc (Lident f) _loc_f in
                (id, (loc_expr _loc_f (Pexp_ident id))))
             (Earley.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x)) lident)])
    let last_record_item = Earley.declare_grammar "last_record_item"
    let _ =
      Earley.set_grammar last_record_item
        (Earley.alternatives
           [Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x)) field)
              (Earley.sequence (Earley.char '=' '=')
                 (expression_lvl (Match, (next_exp Seq)))
                 (fun _  ->
                    fun e  ->
                      fun f  -> let (_loc_f,f) = f in ((id_loc f _loc_f), e)));
           Earley.apply
             (fun f  ->
                let (_loc_f,f) = f in
                let id = id_loc (Lident f) _loc_f in
                (id, (loc_expr _loc_f (Pexp_ident id))))
             (Earley.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x)) lident)])
    let _ =
      set_grammar record_list
        (Earley.alternatives
           [Earley.fsequence
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.sequence record_item semi_col
                          (fun _default_0  -> fun _  -> _default_0)))))
              (Earley.sequence last_record_item
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x) semi_col))
                 (fun it  -> fun _default_0  -> fun l  -> l @ [it]));
           Earley.apply (fun _  -> []) (Earley.empty ())])
    let obj_item = Earley.declare_grammar "obj_item"
    let _ =
      Earley.set_grammar obj_item
        (Earley.fsequence
           (Earley.apply_position
              (fun x  ->
                 fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> ((locate str pos str' pos'), x))
              inst_var_name)
           (Earley.sequence (Earley.char '=' '=')
              (expression_lvl (Match, (next_exp Seq)))
              (fun _  ->
                 fun e  ->
                   fun v  -> let (_loc_v,v) = v in ((id_loc v _loc_v), e))))
    let class_expr_base = Earley.declare_grammar "class_expr_base"
    let _ =
      Earley.set_grammar class_expr_base
        (Earley.alternatives
           [Earley.apply_position
              (fun cp  ->
                 let (_loc_cp,cp) = cp in
                 fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         let cp = id_loc cp _loc_cp in
                         loc_pcl _loc (Pcl_constr (cp, [])))
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 class_path);
           Earley.fsequence_position (Earley.char '[' '[')
             (Earley.fsequence typexpr
                (Earley.fsequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            (Earley.sequence (Earley.char ',' ',') typexpr
                               (fun _  -> fun te  -> te)))))
                   (Earley.sequence (Earley.char ']' ']')
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         class_path)
                      (fun _  ->
                         fun cp  ->
                           let (_loc_cp,cp) = cp in
                           fun tes  ->
                             fun te  ->
                               fun _  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         let cp = id_loc cp _loc_cp in
                                         loc_pcl _loc
                                           (Pcl_constr (cp, (te :: tes)))))));
           Earley.fsequence_position (Earley.string "(" "(")
             (Earley.sequence class_expr (Earley.string ")" ")")
                (fun ce  ->
                   fun _  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               loc_pcl _loc ce.pcl_desc));
           Earley.fsequence_position (Earley.string "(" "(")
             (Earley.fsequence class_expr
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.sequence class_type (Earley.string ")" ")")
                      (fun ct  ->
                         fun _  ->
                           fun _  ->
                             fun ce  ->
                               fun _  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         loc_pcl _loc
                                           (Pcl_constraint (ce, ct))))));
           Earley.fsequence_position fun_kw
             (Earley.fsequence
                (Earley.apply List.rev
                   (Earley.fixpoint1 []
                      (Earley.apply (fun x  -> fun y  -> x :: y)
                         (parameter false))))
                (Earley.sequence arrow_re class_expr
                   (fun _default_0  ->
                      fun ce  ->
                        fun ps  ->
                          fun _default_1  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    apply_params_cls _loc ps ce)));
           Earley.fsequence_position let_kw
             (Earley.fsequence rec_flag
                (Earley.fsequence let_binding
                   (Earley.sequence in_kw class_expr
                      (fun _default_0  ->
                         fun ce  ->
                           fun lbs  ->
                             fun r  ->
                               fun _default_1  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         loc_pcl _loc (Pcl_let (r, lbs, ce))))));
           Earley.fsequence_position object_kw
             (Earley.sequence class_body end_kw
                (fun cb  ->
                   fun _default_0  ->
                     fun _default_1  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               loc_pcl _loc (Pcl_structure cb)))])
    let _ =
      set_grammar class_expr
        (Earley.sequence_position class_expr_base
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.apply List.rev
                    (Earley.fixpoint1 []
                       (Earley.apply (fun x  -> fun y  -> x :: y) argument)))))
           (fun ce  ->
              fun args  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        match args with
                        | None  -> ce
                        | Some l -> loc_pcl _loc (Pcl_apply (ce, l))))
    let class_field = Earley.declare_grammar "class_field"
    let _ =
      Earley.set_grammar class_field
        (Earley.alternatives
           [Earley.fsequence_position inherit_kw
              (Earley.fsequence override_flag
                 (Earley.sequence class_expr
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x)
                          (Earley.sequence as_kw lident
                             (fun _  -> fun _default_0  -> _default_0))))
                    (fun ce  ->
                       fun id  ->
                         fun o  ->
                           fun _default_0  ->
                             fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     loc_pcf _loc (Pcf_inherit (o, ce, id)))));
           Earley.fsequence_position val_kw
             (Earley.fsequence override_flag
                (Earley.fsequence mutable_flag
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         inst_var_name)
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun x  ->
                               fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       ((locate str pos str' pos'), x))
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.sequence (Earley.char ':' ':')
                                     typexpr (fun _  -> fun t  -> t)))))
                         (Earley.sequence (Earley.char '=' '=') expression
                            (fun _  ->
                               fun e  ->
                                 fun te  ->
                                   let (_loc_te,te) = te in
                                   fun ivn  ->
                                     let (_loc_ivn,ivn) = ivn in
                                     fun m  ->
                                       fun o  ->
                                         fun _default_0  ->
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let ivn =
                                                     id_loc ivn _loc_ivn in
                                                   let ex =
                                                     match te with
                                                     | None  -> e
                                                     | Some t ->
                                                         loc_expr _loc_te
                                                           (pexp_constraint
                                                              (e, t)) in
                                                   loc_pcf _loc
                                                     (Pcf_val
                                                        (ivn, m,
                                                          (Cfk_concrete
                                                             (o, ex))))))))));
           Earley.fsequence_position val_kw
             (Earley.fsequence mutable_flag
                (Earley.fsequence virtual_kw
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         inst_var_name)
                      (Earley.sequence (Earley.string ":" ":") typexpr
                         (fun _  ->
                            fun te  ->
                              fun ivn  ->
                                let (_loc_ivn,ivn) = ivn in
                                fun _default_0  ->
                                  fun m  ->
                                    fun _default_1  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              let ivn = id_loc ivn _loc_ivn in
                                              loc_pcf _loc
                                                (Pcf_val
                                                   (ivn, m, (Cfk_virtual te))))))));
           Earley.fsequence_position val_kw
             (Earley.fsequence virtual_kw
                (Earley.fsequence mutable_kw
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         inst_var_name)
                      (Earley.sequence (Earley.string ":" ":") typexpr
                         (fun _  ->
                            fun te  ->
                              fun ivn  ->
                                let (_loc_ivn,ivn) = ivn in
                                fun _default_0  ->
                                  fun _default_1  ->
                                    fun _default_2  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              let ivn = id_loc ivn _loc_ivn in
                                              loc_pcf _loc
                                                (Pcf_val
                                                   (ivn, Mutable,
                                                     (Cfk_virtual te))))))));
           Earley.fsequence_position method_kw
             (Earley.fsequence override_flag
                (Earley.fsequence private_flag
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         method_name)
                      (Earley.fsequence (Earley.string ":" ":")
                         (Earley.fsequence poly_typexpr
                            (Earley.sequence (Earley.char '=' '=') expression
                               (fun _  ->
                                  fun e  ->
                                    fun te  ->
                                      fun _  ->
                                        fun mn  ->
                                          let (_loc_mn,mn) = mn in
                                          fun p  ->
                                            fun o  ->
                                              fun _default_0  ->
                                                fun __loc__start__buf  ->
                                                  fun __loc__start__pos  ->
                                                    fun __loc__end__buf  ->
                                                      fun __loc__end__pos  ->
                                                        let _loc =
                                                          locate
                                                            __loc__start__buf
                                                            __loc__start__pos
                                                            __loc__end__buf
                                                            __loc__end__pos in
                                                        let mn =
                                                          id_loc mn _loc_mn in
                                                        let e =
                                                          loc_expr _loc
                                                            (Pexp_poly
                                                               (e, (Some te))) in
                                                        loc_pcf _loc
                                                          (Pcf_method
                                                             (mn, p,
                                                               (Cfk_concrete
                                                                  (o, e)))))))))));
           Earley.fsequence_position method_kw
             (Earley.fsequence override_flag
                (Earley.fsequence private_flag
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         method_name)
                      (Earley.fsequence (Earley.string ":" ":")
                         (Earley.fsequence poly_syntax_typexpr
                            (Earley.sequence (Earley.char '=' '=') expression
                               (fun _  ->
                                  fun e  ->
                                    fun ((ids,te) as _default_0)  ->
                                      fun _  ->
                                        fun mn  ->
                                          let (_loc_mn,mn) = mn in
                                          fun p  ->
                                            fun o  ->
                                              fun _default_1  ->
                                                fun __loc__start__buf  ->
                                                  fun __loc__start__pos  ->
                                                    fun __loc__end__buf  ->
                                                      fun __loc__end__pos  ->
                                                        let _loc =
                                                          locate
                                                            __loc__start__buf
                                                            __loc__start__pos
                                                            __loc__end__buf
                                                            __loc__end__pos in
                                                        let mn =
                                                          id_loc mn _loc_mn in
                                                        let (e,poly) =
                                                          wrap_type_annotation
                                                            _loc ids te e in
                                                        let e =
                                                          loc_expr _loc
                                                            (Pexp_poly
                                                               (e,
                                                                 (Some poly))) in
                                                        loc_pcf _loc
                                                          (Pcf_method
                                                             (mn, p,
                                                               (Cfk_concrete
                                                                  (o, e)))))))))));
           Earley.fsequence_position method_kw
             (Earley.fsequence override_flag
                (Earley.fsequence private_flag
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         method_name)
                      (Earley.fsequence
                         (Earley.apply List.rev
                            (Earley.fixpoint []
                               (Earley.apply (fun x  -> fun y  -> x :: y)
                                  (Earley.apply
                                     (fun p  ->
                                        let (_loc_p,p) = p in (p, _loc_p))
                                     (Earley.apply_position
                                        (fun x  ->
                                           fun str  ->
                                             fun pos  ->
                                               fun str'  ->
                                                 fun pos'  ->
                                                   ((locate str pos str' pos'),
                                                     x)) (parameter true))))))
                         (Earley.fsequence
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.sequence (Earley.string ":" ":")
                                     typexpr (fun _  -> fun te  -> te))))
                            (Earley.sequence (Earley.char '=' '=') expression
                               (fun _  ->
                                  fun e  ->
                                    fun te  ->
                                      fun ps  ->
                                        fun mn  ->
                                          let (_loc_mn,mn) = mn in
                                          fun p  ->
                                            fun o  ->
                                              fun _default_0  ->
                                                fun __loc__start__buf  ->
                                                  fun __loc__start__pos  ->
                                                    fun __loc__end__buf  ->
                                                      fun __loc__end__pos  ->
                                                        let _loc =
                                                          locate
                                                            __loc__start__buf
                                                            __loc__start__pos
                                                            __loc__end__buf
                                                            __loc__end__pos in
                                                        if
                                                          (ps = []) &&
                                                            (te <> None)
                                                        then give_up ();
                                                        (let mn =
                                                           id_loc mn _loc_mn in
                                                         let e =
                                                           match te with
                                                           | None  -> e
                                                           | Some te ->
                                                               loc_expr _loc
                                                                 (pexp_constraint
                                                                    (e, te)) in
                                                         let e: expression =
                                                           apply_params ps e in
                                                         let e =
                                                           loc_expr _loc
                                                             (Pexp_poly
                                                                (e, None)) in
                                                         loc_pcf _loc
                                                           (Pcf_method
                                                              (mn, p,
                                                                (Cfk_concrete
                                                                   (o, e))))))))))));
           Earley.fsequence_position method_kw
             (Earley.fsequence private_flag
                (Earley.fsequence virtual_kw
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         method_name)
                      (Earley.sequence (Earley.string ":" ":") poly_typexpr
                         (fun _  ->
                            fun pte  ->
                              fun mn  ->
                                let (_loc_mn,mn) = mn in
                                fun _default_0  ->
                                  fun p  ->
                                    fun _default_1  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              let mn = id_loc mn _loc_mn in
                                              loc_pcf _loc
                                                (Pcf_method
                                                   (mn, p, (Cfk_virtual pte))))))));
           Earley.fsequence_position method_kw
             (Earley.fsequence virtual_kw
                (Earley.fsequence private_kw
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         method_name)
                      (Earley.sequence (Earley.string ":" ":") poly_typexpr
                         (fun _  ->
                            fun pte  ->
                              fun mn  ->
                                let (_loc_mn,mn) = mn in
                                fun _default_0  ->
                                  fun _default_1  ->
                                    fun _default_2  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              let mn = id_loc mn _loc_mn in
                                              loc_pcf _loc
                                                (Pcf_method
                                                   (mn, Private,
                                                     (Cfk_virtual pte))))))));
           Earley.fsequence_position constraint_kw
             (Earley.fsequence typexpr
                (Earley.sequence (Earley.char '=' '=') typexpr
                   (fun _  ->
                      fun te'  ->
                        fun te  ->
                          fun _default_0  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    loc_pcf _loc (Pcf_constraint (te, te')))));
           Earley.sequence_position initializer_kw expression
             (fun _default_0  ->
                fun e  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          loc_pcf _loc (Pcf_initializer e))])
    let _ =
      set_grammar class_body
        (Earley.sequence
           (Earley.apply_position
              (fun x  ->
                 fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> ((locate str pos str' pos'), x))
              (Earley.option None (Earley.apply (fun x  -> Some x) pattern)))
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  -> fun y  -> x :: y) class_field)))
           (fun p  ->
              let (_loc_p,p) = p in
              fun f  ->
                let p =
                  match p with
                  | None  -> loc_pat _loc_p Ppat_any
                  | Some p -> p in
                { pcstr_self = p; pcstr_fields = f }))
    let class_binding = Earley.declare_grammar "class_binding"
    let _ =
      Earley.set_grammar class_binding
        (Earley.fsequence_position virtual_flag
           (Earley.fsequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 (Earley.option []
                    (Earley.fsequence (Earley.string "[" "[")
                       (Earley.sequence type_parameters
                          (Earley.string "]" "]")
                          (fun params  -> fun _  -> fun _  -> params)))))
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    class_name)
                 (Earley.fsequence
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             (parameter false))))
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x)
                             (Earley.sequence (Earley.string ":" ":")
                                class_type (fun _  -> fun ct  -> ct))))
                       (Earley.sequence (Earley.char '=' '=') class_expr
                          (fun _  ->
                             fun ce  ->
                               fun ct  ->
                                 fun ps  ->
                                   fun cn  ->
                                     let (_loc_cn,cn) = cn in
                                     fun params  ->
                                       let (_loc_params,params) = params in
                                       fun v  ->
                                         fun __loc__start__buf  ->
                                           fun __loc__start__pos  ->
                                             fun __loc__end__buf  ->
                                               fun __loc__end__pos  ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 let ce =
                                                   apply_params_cls _loc ps
                                                     ce in
                                                 let ce =
                                                   match ct with
                                                   | None  -> ce
                                                   | Some ct ->
                                                       loc_pcl _loc
                                                         (Pcl_constraint
                                                            (ce, ct)) in
                                                 class_type_declaration
                                                   ~attributes:(attach_attrib
                                                                  _loc [])
                                                   _loc_params _loc
                                                   (id_loc cn _loc_cn) params
                                                   v ce)))))))
    let class_definition = Earley.declare_grammar "class_definition"
    let _ =
      Earley.set_grammar class_definition
        (Earley.sequence class_binding
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.sequence and_kw class_binding
                       (fun _  -> fun _default_0  -> _default_0)))))
           (fun cb  -> fun cbs  -> cb :: cbs))
    let pexp_list _loc ?loc_cl  l =
      if l = []
      then loc_expr _loc (pexp_construct ((id_loc (Lident "[]") _loc), None))
      else
        (let loc_cl =
           ghost (match loc_cl with | None  -> _loc | Some pos -> pos) in
         List.fold_right
           (fun (x,pos)  ->
              fun acc  ->
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
      Earley.grammar_family "extra_expressions_grammar"
    let _ =
      extra_expressions_grammar__set__grammar
        (fun lvl  ->
           alternatives (List.map (fun g  -> g lvl) extra_expressions))
    let structure_item_simple = declare_grammar "structure_item_simple"
    let (prefix_expression,prefix_expression__set__grammar) =
      Earley.grammar_family "prefix_expression"
    let _ =
      prefix_expression__set__grammar
        (fun c  ->
           Earley.alternatives
             [Earley.sequence_position function_kw match_cases
                (fun _default_0  ->
                   fun l  ->
                     fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos in
                             {
                               Parsetree.pexp_desc =
                                 (Parsetree.Pexp_function l);
                               Parsetree.pexp_loc = _loc;
                               Parsetree.pexp_attributes = []
                             });
             Earley.fsequence_position match_kw
               (Earley.fsequence expression
                  (Earley.sequence with_kw match_cases
                     (fun _default_0  ->
                        fun l  ->
                          fun e  ->
                            fun _default_1  ->
                              fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos in
                                      {
                                        Parsetree.pexp_desc =
                                          (Parsetree.Pexp_match (e, l));
                                        Parsetree.pexp_loc = _loc;
                                        Parsetree.pexp_attributes = []
                                      })));
             Earley.fsequence_position try_kw
               (Earley.fsequence expression
                  (Earley.sequence with_kw match_cases
                     (fun _default_0  ->
                        fun l  ->
                          fun e  ->
                            fun _default_1  ->
                              fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos in
                                      {
                                        Parsetree.pexp_desc =
                                          (Parsetree.Pexp_try (e, l));
                                        Parsetree.pexp_loc = _loc;
                                        Parsetree.pexp_attributes = []
                                      })));
             alternatives extra_prefix_expressions])
    let (if_expression,if_expression__set__grammar) =
      Earley.grammar_family "if_expression"
    let _ =
      if_expression__set__grammar
        (fun (alm,lvl)  ->
           Earley.alternatives
             [Earley.fsequence_position if_kw
                (Earley.fsequence expression
                   (Earley.fsequence then_kw
                      (Earley.fsequence
                         (expression_lvl (Match, (next_exp Seq)))
                         (Earley.sequence else_kw
                            (expression_lvl (alm, (next_exp Seq)))
                            (fun _default_0  ->
                               fun e'  ->
                                 fun e  ->
                                   fun _default_1  ->
                                     fun c  ->
                                       fun _default_2  ->
                                         fun __loc__start__buf  ->
                                           fun __loc__start__pos  ->
                                             fun __loc__end__buf  ->
                                               fun __loc__end__pos  ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 {
                                                   Parsetree.pexp_desc =
                                                     (Parsetree.Pexp_ifthenelse
                                                        (c, e, (Some e')));
                                                   Parsetree.pexp_loc = _loc;
                                                   Parsetree.pexp_attributes
                                                     = []
                                                 })))));
             Earley.fsequence_position if_kw
               (Earley.fsequence expression
                  (Earley.fsequence then_kw
                     (Earley.sequence (expression_lvl (alm, (next_exp Seq)))
                        no_else
                        (fun e  ->
                           fun _default_0  ->
                             fun _default_1  ->
                               fun c  ->
                                 fun _default_2  ->
                                   fun __loc__start__buf  ->
                                     fun __loc__start__pos  ->
                                       fun __loc__end__buf  ->
                                         fun __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           {
                                             Parsetree.pexp_desc =
                                               (Parsetree.Pexp_ifthenelse
                                                  (c, e, None));
                                             Parsetree.pexp_loc = _loc;
                                             Parsetree.pexp_attributes = []
                                           }))))])
    let _ =
      set_expression_lvl
        (fun ((alm,lvl) as c)  ->
           Earley.alternatives ((extra_expressions_grammar c) ::
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
                                                                    Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (prefix_symbol
                                                                    lvl0))
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
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
                                                                    Earley.fail
                                                                    ())
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
                                                                    Earley.fsequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    left))
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
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
                                                                    fun e  ->
                                                                    fun e' 
                                                                    ->
                                                                    fun
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
                                                                    Earley.fail
                                                                    ())
                                                                    infix_prios)] in
                                                                    if
                                                                    lvl = App
                                                                    then
                                                                    (Earley.sequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    (next_exp
                                                                    App)))
                                                                    (Earley.apply
                                                                    List.rev
                                                                    (Earley.fixpoint1
                                                                    []
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                    argument)))
                                                                    (fun f 
                                                                    ->
                                                                    fun l  ->
                                                                    fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (match 
                                                                    ((f.pexp_desc),
                                                                    l)
                                                                    with
                                                                    | 
                                                                    (Pexp_construct
                                                                    (c,None ),
                                                                    ("",a)::[])
                                                                    ->
                                                                    Pexp_construct
                                                                    (c,
                                                                    (Some a))
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
                                                                    (Earley.fsequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    Dash))
                                                                    (Earley.sequence
                                                                    (Earley.char
                                                                    '#' '#')
                                                                    method_name
                                                                    (fun _ 
                                                                    ->
                                                                    fun f  ->
                                                                    fun e' 
                                                                    ->
                                                                    fun
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
                                                                    (Earley.fsequence_position
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    Dot))
                                                                    (Earley.sequence
                                                                    (Earley.char
                                                                    '.' '.')
                                                                    (Earley.alternatives
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
                                                                    (Earley.apply_position
                                                                    (fun f 
                                                                    ->
                                                                    let 
                                                                    (_loc_f,f)
                                                                    = f in
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
                                                                    let f =
                                                                    id_loc f
                                                                    _loc_f in
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_field
                                                                    (e', f)))
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x)) field))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Aff
                                                                    then
                                                                    (Earley.fsequence_position
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x)) field)
                                                                    (Earley.sequence
                                                                    (Earley.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _ 
                                                                    ->
                                                                    fun e  ->
                                                                    fun f  ->
                                                                    let 
                                                                    (_loc_f,f)
                                                                    = f in
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
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
                                                                    (Earley.fsequence_position
                                                                    (Earley.string
                                                                    "{" "{")
                                                                    (Earley.sequence
                                                                    expression
                                                                    (Earley.string
                                                                    "}" "}")
                                                                    (fun f 
                                                                    ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
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
                                                                    (Earley.fsequence_position
                                                                    (Earley.string
                                                                    "{" "{")
                                                                    (Earley.fsequence
                                                                    expression
                                                                    (Earley.fsequence
                                                                    (Earley.string
                                                                    "}" "}")
                                                                    (Earley.sequence
                                                                    (Earley.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _ 
                                                                    ->
                                                                    fun e  ->
                                                                    fun _  ->
                                                                    fun f  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
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
                                                                    (Earley.fsequence_position
                                                                    (Earley.string
                                                                    "[" "[")
                                                                    (Earley.sequence
                                                                    expression
                                                                    (Earley.string
                                                                    "]" "]")
                                                                    (fun f 
                                                                    ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
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
                                                                    (Earley.fsequence_position
                                                                    (Earley.string
                                                                    "[" "[")
                                                                    (Earley.fsequence
                                                                    expression
                                                                    (Earley.fsequence
                                                                    (Earley.string
                                                                    "]" "]")
                                                                    (Earley.sequence
                                                                    (Earley.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _ 
                                                                    ->
                                                                    fun e  ->
                                                                    fun _  ->
                                                                    fun f  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
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
                                                                    (Earley.fsequence_position
                                                                    (Earley.string
                                                                    "(" "(")
                                                                    (Earley.sequence
                                                                    expression
                                                                    (Earley.string
                                                                    ")" ")")
                                                                    (fun f 
                                                                    ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
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
                                                                    (Earley.fsequence_position
                                                                    (Earley.string
                                                                    "(" "(")
                                                                    (Earley.fsequence
                                                                    expression
                                                                    (Earley.fsequence
                                                                    (Earley.string
                                                                    ")" ")")
                                                                    (Earley.sequence
                                                                    (Earley.string
                                                                    "<-" "<-")
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Aff)))
                                                                    (fun _ 
                                                                    ->
                                                                    fun e  ->
                                                                    fun _  ->
                                                                    fun f  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    fun e' 
                                                                    ->
                                                                    fun _loc 
                                                                    ->
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
                                                                    (fun _ 
                                                                    ->
                                                                    fun r  ->
                                                                    fun e' 
                                                                    ->
                                                                    fun
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
                                                                    r e' _loc)))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl = Seq
                                                                    then
                                                                    (Earley.fsequence
                                                                    (Earley.apply
                                                                    List.rev
                                                                    (Earley.fixpoint
                                                                    []
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                    (Earley.sequence
                                                                    (expression_lvl
                                                                    (LetRight,
                                                                    (next_exp
                                                                    Seq)))
                                                                    semi_col
                                                                    (fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    _default_0)))))
                                                                    (Earley.sequence
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Seq)))
                                                                    (Earley.alternatives
                                                                    [semi_col;
                                                                    no_semi])
                                                                    (fun e' 
                                                                    ->
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    fun ls 
                                                                    ->
                                                                    mk_seq
                                                                    (ls @
                                                                    [e']))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl =
                                                                    Tupl
                                                                    then
                                                                    (Earley.sequence_position
                                                                    (Earley.apply
                                                                    List.rev
                                                                    (Earley.fixpoint1
                                                                    []
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                    (Earley.sequence
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    (next_exp
                                                                    Tupl)))
                                                                    (Earley.char
                                                                    ',' ',')
                                                                    (fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    _default_0)))))
                                                                    (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    (next_exp
                                                                    Tupl)))
                                                                    (fun l 
                                                                    ->
                                                                    fun e' 
                                                                    ->
                                                                    fun
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
                                                                    (Earley.fsequence_position
                                                                    (Earley.ignore_next_blank
                                                                    (Earley.char
                                                                    '$' '$'))
                                                                    (Earley.fsequence
                                                                    (Earley.option
                                                                    "expr"
                                                                    (Earley.sequence
                                                                    (Earley.ignore_next_blank
                                                                    (EarleyStr.regexp
                                                                    ~name:"[a-z]+"
                                                                    "[a-z]+"
                                                                    (fun
                                                                    groupe 
                                                                    ->
                                                                    groupe 0)))
                                                                    (Earley.char
                                                                    ':' ':')
                                                                    (fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    _default_0)))
                                                                    (Earley.sequence
                                                                    (Earley.ignore_next_blank
                                                                    expression)
                                                                    (Earley.char
                                                                    '$' '$')
                                                                    (fun e 
                                                                    ->
                                                                    fun _  ->
                                                                    fun aq 
                                                                    ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    _loc _loc));
                                                                    ((parsetree
                                                                    "pexp_attributes"),
                                                                    (quote_attributes
                                                                    e_loc
                                                                    _loc []))] in
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
                                                                    "float"
                                                                    ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_float")
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
                                                                    "char" ->
                                                                    generic_antiquote
                                                                    (quote_apply
                                                                    e_loc
                                                                    _loc
                                                                    (pa_ast
                                                                    "exp_char")
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
                                                                    () in
                                                                    Quote.pexp_antiquotation
                                                                    _loc f))))
                                                                    :: y
                                                                    else y in
                                                                    if
                                                                    lvl =
                                                                    Atom
                                                                    then
                                                                    (Earley.sequence_position
                                                                    (Earley.ignore_next_blank
                                                                    (Earley.char
                                                                    '$' '$'))
                                                                    uident
                                                                    (fun _ 
                                                                    ->
                                                                    fun c  ->
                                                                    fun
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
                                                                    ()))) ::
                                                                    y
                                                                    else y in
                                                                    if
                                                                    lvl =
                                                                    Atom
                                                                    then
                                                                    (Earley.sequence
                                                                    (Earley.string
                                                                    "<:" "<:")
                                                                    (Earley.alternatives
                                                                    [
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "expr"
                                                                    "expr")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    expression)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_expression
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "type"
                                                                    "type")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    typexpr)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_core_type
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "pat"
                                                                    "pat")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    pattern)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_pattern
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "struct"
                                                                    "struct")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    structure_item_simple)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_structure
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "sig"
                                                                    "sig")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    signature_item)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_signature
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "constructors"
                                                                    "constructors")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    constr_decl_list)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "fields"
                                                                    "fields")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    field_decl_list)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "bindings"
                                                                    "bindings")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    let_binding)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "cases"
                                                                    "cases")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    match_cases)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "module"
                                                                    "module")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_expr)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_module_expr
                                                                    e_loc
                                                                    _loc_e e)));
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "module"
                                                                    "module")
                                                                    (Earley.fsequence
                                                                    (Earley.string
                                                                    "type"
                                                                    "type")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_type)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    let e_loc
                                                                    =
                                                                    exp_ident
                                                                    _loc
                                                                    "_loc" in
                                                                    Quote.quote_module_type
                                                                    e_loc
                                                                    _loc_e e))));
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "record"
                                                                    "record")
                                                                    (Earley.fsequence
                                                                    (Earley.char
                                                                    '<' '<')
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    record_list)
                                                                    (Earley.string
                                                                    ">>" ">>")
                                                                    (fun e 
                                                                    ->
                                                                    let 
                                                                    (_loc_e,e)
                                                                    = e in
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    e_loc  ->
                                                                    fun _loc 
                                                                    ->
                                                                    fun
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
                                                                    (fun _ 
                                                                    ->
                                                                    fun r  ->
                                                                    r)) :: y
                                                                    else y in
                                                                  if
                                                                    lvl =
                                                                    Atom
                                                                  then
                                                                    (
                                                                    Earley.fsequence_position
                                                                    (Earley.string
                                                                    "(" "(")
                                                                    (Earley.fsequence
                                                                    module_kw
                                                                    (Earley.fsequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    module_expr)
                                                                    (Earley.sequence
                                                                    (Earley.apply_position
                                                                    (fun x 
                                                                    ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    (Earley.option
                                                                    None
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Earley.sequence
                                                                    (Earley.string
                                                                    ":" ":")
                                                                    package_type
                                                                    (fun _ 
                                                                    ->
                                                                    fun pt 
                                                                    -> pt)))))
                                                                    (Earley.string
                                                                    ")" ")")
                                                                    (fun pt 
                                                                    ->
                                                                    let 
                                                                    (_loc_pt,pt)
                                                                    = pt in
                                                                    fun _  ->
                                                                    fun me 
                                                                    ->
                                                                    let 
                                                                    (_loc_me,me)
                                                                    = me in
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    fun
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
                                                                  (Earley.fsequence_position
                                                                    (Earley.string
                                                                    "{<" "{<")
                                                                    (Earley.sequence
                                                                    (Earley.option
                                                                    []
                                                                    (Earley.fsequence
                                                                    obj_item
                                                                    (Earley.sequence
                                                                    (Earley.apply
                                                                    List.rev
                                                                    (Earley.fixpoint
                                                                    []
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    ->
                                                                    fun y  ->
                                                                    x :: y)
                                                                    (Earley.sequence
                                                                    semi_col
                                                                    obj_item
                                                                    (fun _ 
                                                                    ->
                                                                    fun o  ->
                                                                    o)))))
                                                                    (Earley.option
                                                                    None
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    semi_col))
                                                                    (fun l 
                                                                    ->
                                                                    fun _  ->
                                                                    fun o  ->
                                                                    o :: l))))
                                                                    (Earley.string
                                                                    ">}" ">}")
                                                                    (fun l 
                                                                    ->
                                                                    fun _  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_override
                                                                    l))))
                                                                  :: y
                                                                else y in
                                                              if lvl = Atom
                                                              then
                                                                (Earley.fsequence_position
                                                                   object_kw
                                                                   (Earley.sequence
                                                                    class_body
                                                                    end_kw
                                                                    (fun o 
                                                                    ->
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    fun
                                                                    _default_1
                                                                     ->
                                                                    fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_object
                                                                    o))))
                                                                :: y
                                                              else y in
                                                            if lvl = Atom
                                                            then
                                                              (Earley.sequence_position
                                                                 new_kw
                                                                 (Earley.apply_position
                                                                    (
                                                                    fun x  ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                    class_path)
                                                                 (fun
                                                                    _default_0
                                                                     ->
                                                                    fun p  ->
                                                                    let 
                                                                    (_loc_p,p)
                                                                    = p in
                                                                    fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_new
                                                                    (id_loc p
                                                                    _loc_p))))
                                                              :: y
                                                            else y in
                                                          if lvl = Atom
                                                          then
                                                            (Earley.fsequence_position
                                                               for_kw
                                                               (Earley.fsequence
                                                                  pattern
                                                                  (Earley.fsequence
                                                                    (Earley.char
                                                                    '=' '=')
                                                                    (Earley.fsequence
                                                                    expression
                                                                    (Earley.fsequence
                                                                    downto_flag
                                                                    (Earley.fsequence
                                                                    expression
                                                                    (Earley.fsequence
                                                                    do_kw
                                                                    (Earley.sequence
                                                                    expression
                                                                    done_kw
                                                                    (fun e'' 
                                                                    ->
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    fun
                                                                    _default_1
                                                                     ->
                                                                    fun e' 
                                                                    ->
                                                                    fun d  ->
                                                                    fun e  ->
                                                                    fun _  ->
                                                                    fun id 
                                                                    ->
                                                                    fun
                                                                    _default_2
                                                                     ->
                                                                    fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_for
                                                                    (id, e,
                                                                    e', d,
                                                                    e'')))))))))))
                                                            :: y
                                                          else y in
                                                        if lvl = Atom
                                                        then
                                                          (Earley.fsequence_position
                                                             while_kw
                                                             (Earley.fsequence
                                                                expression
                                                                (Earley.fsequence
                                                                   do_kw
                                                                   (Earley.sequence
                                                                    expression
                                                                    done_kw
                                                                    (fun e' 
                                                                    ->
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    fun
                                                                    _default_1
                                                                     ->
                                                                    fun e  ->
                                                                    fun
                                                                    _default_2
                                                                     ->
                                                                    fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_while
                                                                    (e, e')))))))
                                                          :: y
                                                        else y in
                                                      if lvl = Atom
                                                      then
                                                        (Earley.fsequence_position
                                                           (Earley.string "{"
                                                              "{")
                                                           (Earley.fsequence
                                                              (Earley.option
                                                                 None
                                                                 (Earley.apply
                                                                    (
                                                                    fun x  ->
                                                                    Some x)
                                                                    (
                                                                    Earley.sequence
                                                                    expression
                                                                    with_kw
                                                                    (fun
                                                                    _default_0
                                                                     ->
                                                                    fun _  ->
                                                                    _default_0))))
                                                              (Earley.sequence
                                                                 record_list
                                                                 (Earley.string
                                                                    "}" "}")
                                                                 (fun l  ->
                                                                    fun _  ->
                                                                    fun e  ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_record
                                                                    (l, e))))))
                                                        :: y
                                                      else y in
                                                    if lvl = Atom
                                                    then
                                                      (Earley.fsequence_position
                                                         (Earley.char '[' '[')
                                                         (Earley.sequence
                                                            expression_list
                                                            (Earley.apply_position
                                                               (fun x  ->
                                                                  fun str  ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                               (Earley.char
                                                                  ']' ']'))
                                                            (fun l  ->
                                                               fun cl  ->
                                                                 let 
                                                                   (_loc_cl,cl)
                                                                   = cl in
                                                                 fun _  ->
                                                                   fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (pexp_list
                                                                    _loc
                                                                    ~loc_cl:_loc_cl
                                                                    l).pexp_desc)))
                                                      :: y
                                                    else y in
                                                  if lvl = Atom
                                                  then
                                                    (Earley.fsequence_position
                                                       (Earley.string "[|"
                                                          "[|")
                                                       (Earley.sequence
                                                          expression_list
                                                          (Earley.string "|]"
                                                             "|]")
                                                          (fun l  ->
                                                             fun _  ->
                                                               fun _  ->
                                                                 fun
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
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_array
                                                                    (List.map
                                                                    fst l)))))
                                                    :: y
                                                  else y in
                                                if lvl = Atom
                                                then
                                                  (Earley.apply_position
                                                     (fun l  ->
                                                        fun __loc__start__buf
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
                                                                loc_expr _loc
                                                                  (Pexp_variant
                                                                    (l, None)))
                                                     tag_name)
                                                  :: y
                                                else y in
                                              if lvl = Atom
                                              then
                                                (Earley.sequence_position
                                                   (Earley.apply_position
                                                      (fun x  ->
                                                         fun str  ->
                                                           fun pos  ->
                                                             fun str'  ->
                                                               fun pos'  ->
                                                                 ((locate str
                                                                    pos str'
                                                                    pos'), x))
                                                      constructor) no_dot
                                                   (fun c  ->
                                                      let (_loc_c,c) = c in
                                                      fun _default_0  ->
                                                        fun __loc__start__buf
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
                                                                loc_expr _loc
                                                                  (pexp_construct
                                                                    ((id_loc
                                                                    c _loc_c),
                                                                    None))))
                                                :: y
                                              else y in
                                            if lvl = App
                                            then
                                              (Earley.sequence_position
                                                 lazy_kw
                                                 (expression_lvl
                                                    (NoMatch, (next_exp App)))
                                                 (fun _default_0  ->
                                                    fun e  ->
                                                      fun __loc__start__buf 
                                                        ->
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
                                                              {
                                                                Parsetree.pexp_desc
                                                                  =
                                                                  (Parsetree.Pexp_lazy
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "e");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    });
                                                                Parsetree.pexp_loc
                                                                  = _loc;
                                                                Parsetree.pexp_attributes
                                                                  = []
                                                              }))
                                              :: y
                                            else y in
                                          if lvl = App
                                          then
                                            (Earley.sequence_position
                                               assert_kw
                                               (Earley.alternatives
                                                  ((Earley.apply_position
                                                      (fun _default_0  ->
                                                         fun
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
                                                                 pexp_assertfalse
                                                                   _loc)
                                                      false_kw) ::
                                                  (let y = [] in
                                                   if lvl = App
                                                   then
                                                     (Earley.sequence
                                                        no_false
                                                        (expression_lvl
                                                           (NoMatch,
                                                             (next_exp App)))
                                                        (fun _  ->
                                                           fun e  ->
                                                             Pexp_assert e))
                                                     :: y
                                                   else y)))
                                               (fun _default_0  ->
                                                  fun e  ->
                                                    fun __loc__start__buf  ->
                                                      fun __loc__start__pos 
                                                        ->
                                                        fun __loc__end__buf 
                                                          ->
                                                          fun __loc__end__pos
                                                             ->
                                                            let _loc =
                                                              locate
                                                                __loc__start__buf
                                                                __loc__start__pos
                                                                __loc__end__buf
                                                                __loc__end__pos in
                                                            loc_expr _loc e))
                                            :: y
                                          else y in
                                        if lvl = Atom
                                        then
                                          (Earley.fsequence_position begin_kw
                                             (Earley.sequence
                                                (Earley.option None
                                                   (Earley.apply
                                                      (fun x  -> Some x)
                                                      expression)) end_kw
                                                (fun e  ->
                                                   fun _default_0  ->
                                                     fun _default_1  ->
                                                       fun __loc__start__buf 
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
                                                               match e with
                                                               | Some e -> e
                                                               | None  ->
                                                                   let cunit
                                                                    =
                                                                    id_loc
                                                                    (Lident
                                                                    "()")
                                                                    _loc in
                                                                   loc_expr
                                                                    _loc
                                                                    (pexp_construct
                                                                    (cunit,
                                                                    None)))))
                                          :: y
                                        else y in
                                      if lvl = Atom
                                      then
                                        (Earley.fsequence_position
                                           (Earley.char '(' '(')
                                           (Earley.fsequence no_parser
                                              (Earley.fsequence expression
                                                 (Earley.sequence
                                                    type_coercion
                                                    (Earley.char ')' ')')
                                                    (fun t  ->
                                                       fun _  ->
                                                         fun e  ->
                                                           fun _default_0  ->
                                                             fun _  ->
                                                               fun
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
                                                                    match t
                                                                    with
                                                                    | 
                                                                    (Some
                                                                    t1,None )
                                                                    ->
                                                                    loc_expr
                                                                    _loc
                                                                    (pexp_constraint
                                                                    (e, t1))
                                                                    | 
                                                                    (t1,Some
                                                                    t2) ->
                                                                    loc_expr
                                                                    _loc
                                                                    (pexp_coerce
                                                                    (e, t1,
                                                                    t2))
                                                                    | 
                                                                    (None
                                                                    ,None )
                                                                    ->
                                                                    assert
                                                                    false)))))
                                        :: y
                                      else y in
                                    if lvl = Atom
                                    then
                                      (Earley.fsequence_position
                                         (Earley.char '(' '(')
                                         (Earley.sequence
                                            (Earley.option None
                                               (Earley.apply
                                                  (fun x  -> Some x)
                                                  expression))
                                            (Earley.char ')' ')')
                                            (fun e  ->
                                               fun _  ->
                                                 fun _  ->
                                                   fun __loc__start__buf  ->
                                                     fun __loc__start__pos 
                                                       ->
                                                       fun __loc__end__buf 
                                                         ->
                                                         fun __loc__end__pos 
                                                           ->
                                                           let _loc =
                                                             locate
                                                               __loc__start__buf
                                                               __loc__start__pos
                                                               __loc__end__buf
                                                               __loc__end__pos in
                                                           match e with
                                                           | Some e ->
                                                               if
                                                                 e.pexp_desc
                                                                   ==
                                                                   Quote.dummy_pexp
                                                               then e
                                                               else
                                                                 loc_expr
                                                                   _loc
                                                                   e.pexp_desc
                                                           | None  ->
                                                               let cunit =
                                                                 id_loc
                                                                   (Lident
                                                                    "()")
                                                                   _loc in
                                                               loc_expr _loc
                                                                 (pexp_construct
                                                                    (cunit,
                                                                    None)))))
                                      :: y
                                    else y in
                                  if (allow_let alm) && (lvl < App)
                                  then
                                    (Earley.sequence_position let_kw
                                       (Earley.alternatives
                                          (let y =
                                             [Earley.fsequence_position
                                                module_kw
                                                (Earley.fsequence module_name
                                                   (Earley.fsequence
                                                      (Earley.apply List.rev
                                                         (Earley.fixpoint []
                                                            (Earley.apply
                                                               (fun x  ->
                                                                  fun y  -> x
                                                                    :: y)
                                                               (Earley.fsequence_position
                                                                  (Earley.char
                                                                    '(' '(')
                                                                  (Earley.fsequence
                                                                    module_name
                                                                    (Earley.sequence
                                                                    (Earley.option
                                                                    None
                                                                    (Earley.apply
                                                                    (fun x 
                                                                    -> Some x)
                                                                    (Earley.sequence
                                                                    (Earley.char
                                                                    ':' ':')
                                                                    module_type
                                                                    (fun _ 
                                                                    ->
                                                                    fun mt 
                                                                    -> mt))))
                                                                    (Earley.char
                                                                    ')' ')')
                                                                    (fun mt 
                                                                    ->
                                                                    fun _  ->
                                                                    fun mn 
                                                                    ->
                                                                    fun _  ->
                                                                    fun
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
                                                                    (mn, mt,
                                                                    _loc))))))))
                                                      (Earley.fsequence
                                                         (Earley.apply_position
                                                            (fun x  ->
                                                               fun str  ->
                                                                 fun pos  ->
                                                                   fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                            (Earley.option
                                                               None
                                                               (Earley.apply
                                                                  (fun x  ->
                                                                    Some x)
                                                                  (Earley.sequence
                                                                    (Earley.string
                                                                    ":" ":")
                                                                    module_type
                                                                    (fun _ 
                                                                    ->
                                                                    fun mt 
                                                                    -> mt)))))
                                                         (Earley.fsequence
                                                            (Earley.string
                                                               "=" "=")
                                                            (Earley.fsequence
                                                               (Earley.apply_position
                                                                  (fun x  ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                  module_expr)
                                                               (Earley.sequence
                                                                  in_kw
                                                                  (expression_lvl
                                                                    ((right_alm
                                                                    alm),
                                                                    Seq))
                                                                  (fun
                                                                    _default_0
                                                                     ->
                                                                    fun e  ->
                                                                    fun me 
                                                                    ->
                                                                    let 
                                                                    (_loc_me,me)
                                                                    = me in
                                                                    fun _  ->
                                                                    fun mt 
                                                                    ->
                                                                    let 
                                                                    (_loc_mt,mt)
                                                                    = mt in
                                                                    fun l  ->
                                                                    fun mn 
                                                                    ->
                                                                    fun
                                                                    _default_1
                                                                     ->
                                                                    fun
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
                                                                    ->
                                                                    fun
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
                                             Earley.fsequence_position
                                               open_kw
                                               (Earley.fsequence
                                                  override_flag
                                                  (Earley.fsequence
                                                     (Earley.apply_position
                                                        (fun x  ->
                                                           fun str  ->
                                                             fun pos  ->
                                                               fun str'  ->
                                                                 fun pos'  ->
                                                                   ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                        module_path)
                                                     (Earley.sequence in_kw
                                                        (expression_lvl
                                                           ((right_alm alm),
                                                             Seq))
                                                        (fun _default_0  ->
                                                           fun e  ->
                                                             fun mp  ->
                                                               let (_loc_mp,mp)
                                                                 = mp in
                                                               fun o  ->
                                                                 fun
                                                                   _default_1
                                                                    ->
                                                                   fun
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
                                                                    let mp =
                                                                    id_loc mp
                                                                    _loc_mp in
                                                                    fun _loc 
                                                                    ->
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_open
                                                                    (o, mp,
                                                                    e))))))] in
                                           if (allow_let alm) && (lvl < App)
                                           then
                                             (Earley.fsequence_position
                                                rec_flag
                                                (Earley.fsequence let_binding
                                                   (Earley.fsequence in_kw
                                                      (Earley.sequence
                                                         (expression_lvl
                                                            ((right_alm alm),
                                                              Seq)) no_semi
                                                         (fun e  ->
                                                            fun _default_0 
                                                              ->
                                                              fun _default_1 
                                                                ->
                                                                fun l  ->
                                                                  fun r  ->
                                                                    fun
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
                                                                    fun _loc 
                                                                    ->
                                                                    loc_expr
                                                                    _loc
                                                                    (Pexp_let
                                                                    (r, l, e)))))))
                                             :: y
                                           else y))
                                       (fun _default_0  ->
                                          fun r  ->
                                            fun __loc__start__buf  ->
                                              fun __loc__start__pos  ->
                                                fun __loc__end__buf  ->
                                                  fun __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    r _loc))
                                    :: y
                                  else y in
                                if (allow_let alm) && (lvl < App)
                                then
                                  (Earley.fsequence_position fun_kw
                                     (Earley.fsequence
                                        (Earley.apply List.rev
                                           (Earley.fixpoint []
                                              (Earley.apply
                                                 (fun x  -> fun y  -> x :: y)
                                                 (Earley.apply
                                                    (fun lbl  ->
                                                       let (_loc_lbl,lbl) =
                                                         lbl in
                                                       (lbl, _loc_lbl))
                                                    (Earley.apply_position
                                                       (fun x  ->
                                                          fun str  ->
                                                            fun pos  ->
                                                              fun str'  ->
                                                                fun pos'  ->
                                                                  ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                       (parameter true))))))
                                        (Earley.fsequence arrow_re
                                           (Earley.sequence
                                              (expression_lvl
                                                 ((right_alm alm), Seq))
                                              no_semi
                                              (fun e  ->
                                                 fun _default_0  ->
                                                   fun _default_1  ->
                                                     fun l  ->
                                                       fun _default_2  ->
                                                         fun
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
                                                                 loc_expr
                                                                   _loc
                                                                   (apply_params
                                                                    l e).pexp_desc)))))
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
                            (Earley.fsequence_position
                               (Earley.apply_position
                                  (fun x  ->
                                     fun str  ->
                                       fun pos  ->
                                         fun str'  ->
                                           fun pos'  ->
                                             ((locate str pos str' pos'), x))
                                  module_path)
                               (Earley.fsequence (Earley.char '.' '.')
                                  (Earley.fsequence (Earley.char '{' '{')
                                     (Earley.fsequence
                                        (Earley.option None
                                           (Earley.apply (fun x  -> Some x)
                                              (Earley.sequence expression
                                                 with_kw
                                                 (fun _default_0  ->
                                                    fun _  -> _default_0))))
                                        (Earley.sequence record_list
                                           (Earley.char '}' '}')
                                           (fun l  ->
                                              fun _  ->
                                                fun e  ->
                                                  fun _  ->
                                                    fun _  ->
                                                      fun mp  ->
                                                        let (_loc_mp,mp) = mp in
                                                        fun __loc__start__buf
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
                                                                let mp =
                                                                  id_loc mp
                                                                    _loc_mp in
                                                                loc_expr _loc
                                                                  (Pexp_open
                                                                    (Fresh,
                                                                    mp,
                                                                    (loc_expr
                                                                    _loc
                                                                    (Pexp_record
                                                                    (l, e)))))))))))
                            :: y
                          else y in
                        if lvl = Atom
                        then
                          (Earley.fsequence_position
                             (Earley.apply_position
                                (fun x  ->
                                   fun str  ->
                                     fun pos  ->
                                       fun str'  ->
                                         fun pos'  ->
                                           ((locate str pos str' pos'), x))
                                module_path)
                             (Earley.fsequence (Earley.char '.' '.')
                                (Earley.fsequence (Earley.char '[' '[')
                                   (Earley.sequence expression_list
                                      (Earley.apply_position
                                         (fun x  ->
                                            fun str  ->
                                              fun pos  ->
                                                fun str'  ->
                                                  fun pos'  ->
                                                    ((locate str pos str'
                                                        pos'), x))
                                         (Earley.char ']' ']'))
                                      (fun l  ->
                                         fun cl  ->
                                           let (_loc_cl,cl) = cl in
                                           fun _  ->
                                             fun _  ->
                                               fun mp  ->
                                                 let (_loc_mp,mp) = mp in
                                                 fun __loc__start__buf  ->
                                                   fun __loc__start__pos  ->
                                                     fun __loc__end__buf  ->
                                                       fun __loc__end__pos 
                                                         ->
                                                         let _loc =
                                                           locate
                                                             __loc__start__buf
                                                             __loc__start__pos
                                                             __loc__end__buf
                                                             __loc__end__pos in
                                                         let mp =
                                                           id_loc mp _loc_mp in
                                                         loc_expr _loc
                                                           (Pexp_open
                                                              (Fresh, mp,
                                                                (loc_expr
                                                                   _loc
                                                                   (pexp_list
                                                                    _loc
                                                                    ~loc_cl:_loc_cl
                                                                    l).pexp_desc))))))))
                          :: y
                        else y in
                      if lvl = Atom
                      then
                        (Earley.fsequence_position
                           (Earley.apply_position
                              (fun x  ->
                                 fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         ((locate str pos str' pos'), x))
                              module_path)
                           (Earley.fsequence (Earley.string "." ".")
                              (Earley.fsequence (Earley.string "(" "(")
                                 (Earley.sequence expression
                                    (Earley.string ")" ")")
                                    (fun e  ->
                                       fun _  ->
                                         fun _  ->
                                           fun _  ->
                                             fun mp  ->
                                               let (_loc_mp,mp) = mp in
                                               fun __loc__start__buf  ->
                                                 fun __loc__start__pos  ->
                                                   fun __loc__end__buf  ->
                                                     fun __loc__end__pos  ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       let mp =
                                                         id_loc mp _loc_mp in
                                                       loc_expr _loc
                                                         (Pexp_open
                                                            (Fresh, mp, e)))))))
                        :: y
                      else y in
                    if lvl = Atom
                    then
                      (Earley.apply_position
                         (fun c  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    loc_expr _loc (Pexp_constant c)) constant)
                      :: y
                    else y in
                  if lvl = Atom
                  then
                    (Earley.apply_position
                       (fun id  ->
                          let (_loc_id,id) = id in
                          fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  loc_expr _loc
                                    (Pexp_ident (id_loc id _loc_id)))
                       (Earley.apply_position
                          (fun x  ->
                             fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     ((locate str pos str' pos'), x))
                          value_path))
                    :: y
                  else y in
                if lvl = Aff
                then
                  (Earley.fsequence_position
                     (Earley.apply_position
                        (fun x  ->
                           fun str  ->
                             fun pos  ->
                               fun str'  ->
                                 fun pos'  -> ((locate str pos str' pos'), x))
                        inst_var_name)
                     (Earley.sequence (Earley.string "<-" "<-")
                        (expression_lvl ((right_alm alm), (next_exp Aff)))
                        (fun _  ->
                           fun e  ->
                             fun v  ->
                               let (_loc_v,v) = v in
                               fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       loc_expr _loc
                                         (Pexp_setinstvar
                                            ((id_loc v _loc_v), e)))))
                  :: y
                else y in
              if (lvl < Atom) && (lvl != Seq)
              then (expression_lvl ((left_alm alm), (next_exp lvl))) :: y
              else y)))
    let module_expr_base = Earley.declare_grammar "module_expr_base"
    let _ =
      Earley.set_grammar module_expr_base
        (Earley.alternatives
           [Earley.apply_position
              (fun mp  ->
                 fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         let mid = id_loc mp _loc in
                         mexpr_loc _loc (Pmod_ident mid)) module_path;
           Earley.fsequence_position struct_kw
             (Earley.sequence structure end_kw
                (fun ms  ->
                   fun _default_0  ->
                     fun _default_1  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               mexpr_loc _loc (Pmod_structure ms)));
           Earley.fsequence_position functor_kw
             (Earley.fsequence (Earley.char '(' '(')
                (Earley.fsequence module_name
                   (Earley.fsequence
                      (Earley.option None
                         (Earley.apply (fun x  -> Some x)
                            (Earley.sequence (Earley.char ':' ':')
                               module_type (fun _  -> fun mt  -> mt))))
                      (Earley.fsequence (Earley.char ')' ')')
                         (Earley.sequence arrow_re module_expr
                            (fun _default_0  ->
                               fun me  ->
                                 fun _  ->
                                   fun mt  ->
                                     fun mn  ->
                                       fun _  ->
                                         fun _default_1  ->
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   mexpr_loc _loc
                                                     (Pmod_functor
                                                        (mn, mt, me))))))));
           Earley.fsequence_position (Earley.char '(' '(')
             (Earley.fsequence module_expr
                (Earley.sequence
                   (Earley.option None
                      (Earley.apply (fun x  -> Some x)
                         (Earley.sequence (Earley.char ':' ':') module_type
                            (fun _  -> fun mt  -> mt))))
                   (Earley.char ')' ')')
                   (fun mt  ->
                      fun _  ->
                        fun me  ->
                          fun _  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    match mt with
                                    | None  -> me
                                    | Some mt ->
                                        mexpr_loc _loc
                                          (Pmod_constraint (me, mt)))));
           Earley.fsequence_position (Earley.char '(' '(')
             (Earley.fsequence val_kw
                (Earley.fsequence expression
                   (Earley.sequence
                      (Earley.apply_position
                         (fun x  ->
                            fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    ((locate str pos str' pos'), x))
                         (Earley.option None
                            (Earley.apply (fun x  -> Some x)
                               (Earley.sequence (Earley.string ":" ":")
                                  package_type (fun _  -> fun pt  -> pt)))))
                      (Earley.char ')' ')')
                      (fun pt  ->
                         let (_loc_pt,pt) = pt in
                         fun _  ->
                           fun e  ->
                             fun _default_0  ->
                               fun _  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         let e =
                                           match pt with
                                           | None  -> Pmod_unpack e
                                           | Some pt ->
                                               let pt = loc_typ _loc_pt pt in
                                               Pmod_unpack
                                                 (loc_expr _loc
                                                    (pexp_constraint (e, pt))) in
                                         mexpr_loc _loc e))))])
    let _ =
      set_grammar module_expr
        (Earley.sequence
           (Earley.apply_position
              (fun x  ->
                 fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> ((locate str pos str' pos'), x))
              module_expr_base)
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.fsequence_position (Earley.string "(" "(")
                       (Earley.sequence module_expr (Earley.string ")" ")")
                          (fun m  ->
                             fun _  ->
                               fun _  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         (_loc, m)))))))
           (fun m  ->
              let (_loc_m,m) = m in
              fun l  ->
                List.fold_left
                  (fun acc  ->
                     fun (_loc_n,n)  ->
                       mexpr_loc (merge2 _loc_m _loc_n) (Pmod_apply (acc, n)))
                  m l))
    let module_type_base = Earley.declare_grammar "module_type_base"
    let _ =
      Earley.set_grammar module_type_base
        (Earley.alternatives
           [Earley.apply_position
              (fun mp  ->
                 fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         let mid = id_loc mp _loc in
                         mtyp_loc _loc (Pmty_ident mid)) modtype_path;
           Earley.fsequence_position sig_kw
             (Earley.sequence signature end_kw
                (fun ms  ->
                   fun _default_0  ->
                     fun _default_1  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               mtyp_loc _loc (Pmty_signature ms)));
           Earley.fsequence_position functor_kw
             (Earley.fsequence (Earley.char '(' '(')
                (Earley.fsequence module_name
                   (Earley.fsequence
                      (Earley.option None
                         (Earley.apply (fun x  -> Some x)
                            (Earley.sequence (Earley.char ':' ':')
                               module_type (fun _  -> fun mt  -> mt))))
                      (Earley.fsequence (Earley.char ')' ')')
                         (Earley.fsequence arrow_re
                            (Earley.sequence module_type no_with
                               (fun me  ->
                                  fun _default_0  ->
                                    fun _default_1  ->
                                      fun _  ->
                                        fun mt  ->
                                          fun mn  ->
                                            fun _  ->
                                              fun _default_2  ->
                                                fun __loc__start__buf  ->
                                                  fun __loc__start__pos  ->
                                                    fun __loc__end__buf  ->
                                                      fun __loc__end__pos  ->
                                                        let _loc =
                                                          locate
                                                            __loc__start__buf
                                                            __loc__start__pos
                                                            __loc__end__buf
                                                            __loc__end__pos in
                                                        mtyp_loc _loc
                                                          (Pmty_functor
                                                             (mn, mt, me)))))))));
           Earley.fsequence (Earley.string "(" "(")
             (Earley.sequence module_type (Earley.string ")" ")")
                (fun mt  -> fun _  -> fun _  -> mt));
           Earley.fsequence_position module_kw
             (Earley.fsequence type_kw
                (Earley.sequence of_kw module_expr
                   (fun _default_0  ->
                      fun me  ->
                        fun _default_1  ->
                          fun _default_2  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    mtyp_loc _loc (Pmty_typeof me))))])
    let mod_constraint = Earley.declare_grammar "mod_constraint"
    let _ =
      Earley.set_grammar mod_constraint
        (Earley.alternatives
           [Earley.sequence
              (Earley.apply_position
                 (fun x  ->
                    fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  -> ((locate str pos str' pos'), x))
                 type_kw) typedef_in_constraint
              (fun t  ->
                 let (_loc_t,t) = t in
                 fun tf  ->
                   let (tn,ty) = tf (Some _loc_t) in Pwith_type (tn, ty));
           Earley.fsequence module_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   module_path)
                (Earley.sequence (Earley.char '=' '=')
                   (Earley.apply_position
                      (fun x  ->
                         fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  -> ((locate str pos str' pos'), x))
                      extended_module_path)
                   (fun _  ->
                      fun m2  ->
                        let (_loc_m2,m2) = m2 in
                        fun m1  ->
                          let (_loc_m1,m1) = m1 in
                          fun _default_0  ->
                            let name = id_loc m1 _loc_m1 in
                            Pwith_module (name, (id_loc m2 _loc_m2)))));
           Earley.fsequence_position type_kw
             (Earley.fsequence (Earley.option [] type_params)
                (Earley.fsequence
                   (Earley.apply_position
                      (fun x  ->
                         fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  -> ((locate str pos str' pos'), x))
                      typeconstr_name)
                   (Earley.sequence (Earley.string ":=" ":=") typexpr
                      (fun _  ->
                         fun te  ->
                           fun tcn  ->
                             let (_loc_tcn,tcn) = tcn in
                             fun tps  ->
                               fun _default_0  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         let td =
                                           type_declaration _loc
                                             (id_loc tcn _loc_tcn) tps []
                                             Ptype_abstract Public (Some te) in
                                         Pwith_typesubst td))));
           Earley.fsequence module_kw
             (Earley.fsequence module_name
                (Earley.sequence (Earley.string ":=" ":=")
                   (Earley.apply_position
                      (fun x  ->
                         fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  -> ((locate str pos str' pos'), x))
                      extended_module_path)
                   (fun _  ->
                      fun emp  ->
                        let (_loc_emp,emp) = emp in
                        fun mn  ->
                          fun _default_0  ->
                            Pwith_modsubst (mn, (id_loc emp _loc_emp)))))])
    let _ =
      set_grammar module_type
        (Earley.sequence_position module_type_base
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence with_kw
                    (Earley.sequence mod_constraint
                       (Earley.apply List.rev
                          (Earley.fixpoint []
                             (Earley.apply (fun x  -> fun y  -> x :: y)
                                (Earley.sequence and_kw mod_constraint
                                   (fun _  -> fun _default_0  -> _default_0)))))
                       (fun m  -> fun l  -> fun _  -> m :: l)))))
           (fun m  ->
              fun l  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        match l with
                        | None  -> m
                        | Some l -> mtyp_loc _loc (Pmty_with (m, l))))
    let structure_item_base = Earley.declare_grammar "structure_item_base"
    let _ =
      Earley.set_grammar structure_item_base
        (Earley.alternatives
           [Earley.fsequence_position
              (EarleyStr.regexp ~name:"let" let_re (fun groupe  -> groupe 0))
              (Earley.sequence rec_flag let_binding
                 (fun r  ->
                    fun l  ->
                      fun _default_0  ->
                        fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos in
                                loc_str _loc
                                  (match l with
                                   | { pvb_pat = { ppat_desc = Ppat_any  };
                                       pvb_expr = e }::[] -> pstr_eval e
                                   | _ -> Pstr_value (r, l))));
           Earley.fsequence_position external_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   value_name)
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.fsequence typexpr
                      (Earley.fsequence (Earley.string "=" "=")
                         (Earley.sequence
                            (Earley.apply List.rev
                               (Earley.fixpoint []
                                  (Earley.apply (fun x  -> fun y  -> x :: y)
                                     string_litteral))) post_item_attributes
                            (fun ls  ->
                               fun a  ->
                                 fun _  ->
                                   fun ty  ->
                                     fun _  ->
                                       fun n  ->
                                         let (_loc_n,n) = n in
                                         fun _default_0  ->
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let l = List.length ls in
                                                   if (l < 1) || (l > 3)
                                                   then give_up ();
                                                   loc_str _loc
                                                     (Pstr_primitive
                                                        {
                                                          pval_name =
                                                            (id_loc n _loc_n);
                                                          pval_type = ty;
                                                          pval_prim = ls;
                                                          pval_loc = _loc;
                                                          pval_attributes =
                                                            (attach_attrib
                                                               _loc a)
                                                        })))))));
           Earley.apply_position
             (fun td  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_str _loc (Pstr_type (List.map snd td)))
             type_definition;
           Earley.apply_position
             (fun ex  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_str _loc ex) exception_definition;
           Earley.sequence module_kw
             (Earley.alternatives
                [Earley.fsequence_position rec_kw
                   (Earley.fsequence module_name
                      (Earley.fsequence
                         (Earley.option None
                            (Earley.apply (fun x  -> Some x)
                               (Earley.sequence (Earley.string ":" ":")
                                  module_type (fun _  -> fun mt  -> mt))))
                         (Earley.fsequence (Earley.char '=' '=')
                            (Earley.sequence module_expr
                               (Earley.apply List.rev
                                  (Earley.fixpoint []
                                     (Earley.apply
                                        (fun x  -> fun y  -> x :: y)
                                        (Earley.fsequence_position and_kw
                                           (Earley.fsequence module_name
                                              (Earley.fsequence
                                                 (Earley.option None
                                                    (Earley.apply
                                                       (fun x  -> Some x)
                                                       (Earley.sequence
                                                          (Earley.string ":"
                                                             ":") module_type
                                                          (fun _  ->
                                                             fun mt  -> mt))))
                                                 (Earley.sequence
                                                    (Earley.char '=' '=')
                                                    module_expr
                                                    (fun _  ->
                                                       fun me  ->
                                                         fun mt  ->
                                                           fun mn  ->
                                                             fun _default_0 
                                                               ->
                                                               fun
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
                                                                    module_binding
                                                                    _loc mn
                                                                    mt me))))))))
                               (fun me  ->
                                  fun ms  ->
                                    fun _  ->
                                      fun mt  ->
                                        fun mn  ->
                                          fun _default_0  ->
                                            fun __loc__start__buf  ->
                                              fun __loc__start__pos  ->
                                                fun __loc__end__buf  ->
                                                  fun __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    let m =
                                                      module_binding _loc mn
                                                        mt me in
                                                    loc_str _loc
                                                      (Pstr_recmodule (m ::
                                                         ms)))))));
                Earley.fsequence_position module_name
                  (Earley.fsequence
                     (Earley.apply List.rev
                        (Earley.fixpoint []
                           (Earley.apply (fun x  -> fun y  -> x :: y)
                              (Earley.fsequence_position
                                 (Earley.string "(" "(")
                                 (Earley.fsequence module_name
                                    (Earley.sequence
                                       (Earley.option None
                                          (Earley.apply (fun x  -> Some x)
                                             (Earley.sequence
                                                (Earley.string ":" ":")
                                                module_type
                                                (fun _  -> fun mt  -> mt))))
                                       (Earley.string ")" ")")
                                       (fun mt  ->
                                          fun _  ->
                                            fun mn  ->
                                              fun _  ->
                                                fun __loc__start__buf  ->
                                                  fun __loc__start__pos  ->
                                                    fun __loc__end__buf  ->
                                                      fun __loc__end__pos  ->
                                                        let _loc =
                                                          locate
                                                            __loc__start__buf
                                                            __loc__start__pos
                                                            __loc__end__buf
                                                            __loc__end__pos in
                                                        (mn, mt, _loc))))))))
                     (Earley.fsequence
                        (Earley.apply_position
                           (fun x  ->
                              fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      ((locate str pos str' pos'), x))
                           (Earley.option None
                              (Earley.apply (fun x  -> Some x)
                                 (Earley.sequence (Earley.string ":" ":")
                                    module_type (fun _  -> fun mt  -> mt)))))
                        (Earley.sequence (Earley.string "=" "=")
                           (Earley.apply_position
                              (fun x  ->
                                 fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         ((locate str pos str' pos'), x))
                              module_expr)
                           (fun _  ->
                              fun me  ->
                                let (_loc_me,me) = me in
                                fun mt  ->
                                  let (_loc_mt,mt) = mt in
                                  fun l  ->
                                    fun mn  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              let me =
                                                match mt with
                                                | None  -> me
                                                | Some mt ->
                                                    mexpr_loc
                                                      (merge2 _loc_mt _loc_me)
                                                      (Pmod_constraint
                                                         (me, mt)) in
                                              let me =
                                                List.fold_left
                                                  (fun acc  ->
                                                     fun (mn,mt,_loc)  ->
                                                       mexpr_loc
                                                         (merge2 _loc _loc_me)
                                                         (Pmod_functor
                                                            (mn, mt, acc)))
                                                  me (List.rev l) in
                                              loc_str _loc
                                                (Pstr_module
                                                   (module_binding _loc mn
                                                      None me))))));
                Earley.fsequence_position type_kw
                  (Earley.fsequence
                     (Earley.apply_position
                        (fun x  ->
                           fun str  ->
                             fun pos  ->
                               fun str'  ->
                                 fun pos'  -> ((locate str pos str' pos'), x))
                        modtype_name)
                     (Earley.sequence
                        (Earley.option None
                           (Earley.apply (fun x  -> Some x)
                              (Earley.sequence (Earley.string "=" "=")
                                 module_type (fun _  -> fun mt  -> mt))))
                        post_item_attributes
                        (fun mt  ->
                           fun a  ->
                             fun mn  ->
                               let (_loc_mn,mn) = mn in
                               fun _default_0  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         loc_str _loc
                                           (Pstr_modtype
                                              {
                                                pmtd_name =
                                                  (id_loc mn _loc_mn);
                                                pmtd_type = mt;
                                                pmtd_attributes =
                                                  (attach_attrib _loc a);
                                                pmtd_loc = _loc
                                              }))))])
             (fun _default_0  -> fun r  -> r);
           Earley.fsequence_position open_kw
             (Earley.fsequence override_flag
                (Earley.sequence
                   (Earley.apply_position
                      (fun x  ->
                         fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  -> ((locate str pos str' pos'), x))
                      module_path) post_item_attributes
                   (fun m  ->
                      let (_loc_m,m) = m in
                      fun a  ->
                        fun o  ->
                          fun _default_0  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    loc_str _loc
                                      (Pstr_open
                                         {
                                           popen_lid = (id_loc m _loc_m);
                                           popen_override = o;
                                           popen_loc = _loc;
                                           popen_attributes =
                                             (attach_attrib _loc a)
                                         }))));
           Earley.fsequence_position include_kw
             (Earley.sequence module_expr post_item_attributes
                (fun me  ->
                   fun a  ->
                     fun _default_0  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               loc_str _loc
                                 (Pstr_include
                                    {
                                      pincl_mod = me;
                                      pincl_loc = _loc;
                                      pincl_attributes =
                                        (attach_attrib _loc a)
                                    })));
           Earley.sequence_position class_kw
             (Earley.alternatives
                [Earley.apply (fun ctd  -> Pstr_class_type ctd)
                   classtype_definition;
                Earley.apply (fun cds  -> Pstr_class cds) class_definition])
             (fun _default_0  ->
                fun r  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          loc_str _loc r);
           Earley.fsequence_position (Earley.string "$struct:" "$struct:")
             (Earley.sequence (Earley.ignore_next_blank expression)
                (Earley.char '$' '$')
                (fun e  ->
                   fun _  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               let open Quote in
                                 pstr_antiquotation _loc
                                   (function
                                    | Quote_pstr  ->
                                        let e_loc = exp_ident _loc "_loc" in
                                        quote_apply e_loc _loc
                                          (pa_ast "loc_str")
                                          [quote_location_t e_loc _loc _loc;
                                          quote_const e_loc _loc
                                            (parsetree "Pstr_include")
                                            [quote_record e_loc _loc
                                               [((parsetree "pincl_loc"),
                                                  (quote_location_t e_loc
                                                     _loc _loc));
                                               ((parsetree "pincl_attributes"),
                                                 (quote_list quote_attribute
                                                    e_loc _loc []));
                                               ((parsetree "pincl_mod"),
                                                 (quote_apply e_loc _loc
                                                    (pa_ast "mexpr_loc")
                                                    [quote_location_t e_loc
                                                       _loc _loc;
                                                    quote_const e_loc _loc
                                                      (parsetree
                                                         "Pmod_structure")
                                                      [e]]))]]]
                                    | _ -> failwith "Bad antiquotation...")))])
    let structure_item_aux = Earley.declare_grammar "structure_item_aux"
    let _ =
      Earley.set_grammar structure_item_aux
        (Earley.alternatives
           [Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.apply_position
             (fun e  ->
                let (_loc_e,e) = e in
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        (attach_str _loc) @ [loc_str _loc_e (pstr_eval e)])
             (Earley.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x))
                expression);
           Earley.fsequence structure_item_aux
             (Earley.sequence (Earley.option () double_semi_col)
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   (alternatives extra_structure))
                (fun _default_0  ->
                   fun e  ->
                     let (_loc_e,e) = e in
                     fun s1  ->
                       List.rev_append e
                         (List.rev_append (attach_str _loc_e) s1)));
           Earley.fsequence structure_item_aux
             (Earley.sequence (Earley.option () double_semi_col)
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   structure_item_base)
                (fun _default_0  ->
                   fun s2  ->
                     let (_loc_s2,s2) = s2 in
                     fun s1  -> s2 ::
                       (List.rev_append (attach_str _loc_s2) s1)));
           Earley.fsequence structure_item_aux
             (Earley.sequence double_semi_col
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   expression)
                (fun _default_0  ->
                   fun e  ->
                     let (_loc_e,e) = e in
                     fun s1  -> (loc_str _loc_e (pstr_eval e)) ::
                       (List.rev_append (attach_str _loc_e) s1)))])
    let _ =
      set_grammar structure_item
        (Earley.sequence structure_item_aux
           (Earley.option () double_semi_col)
           (fun l  -> fun _default_0  -> List.rev l))
    let _ =
      set_grammar structure_item_simple
        (Earley.apply List.rev
           (Earley.fixpoint []
              (Earley.apply (fun x  -> fun y  -> x :: y) structure_item_base)))
    let signature_item_base = Earley.declare_grammar "signature_item_base"
    let _ =
      Earley.set_grammar signature_item_base
        (Earley.alternatives
           [Earley.fsequence_position val_kw
              (Earley.fsequence
                 (Earley.apply_position
                    (fun x  ->
                       fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  -> ((locate str pos str' pos'), x))
                    value_name)
                 (Earley.fsequence (Earley.string ":" ":")
                    (Earley.sequence typexpr post_item_attributes
                       (fun ty  ->
                          fun a  ->
                            fun _  ->
                              fun n  ->
                                let (_loc_n,n) = n in
                                fun _default_0  ->
                                  fun __loc__start__buf  ->
                                    fun __loc__start__pos  ->
                                      fun __loc__end__buf  ->
                                        fun __loc__end__pos  ->
                                          let _loc =
                                            locate __loc__start__buf
                                              __loc__start__pos
                                              __loc__end__buf __loc__end__pos in
                                          loc_sig _loc
                                            (psig_value
                                               ~attributes:(attach_attrib
                                                              _loc a) _loc
                                               (id_loc n _loc_n) ty [])))));
           Earley.fsequence_position external_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   value_name)
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.fsequence typexpr
                      (Earley.fsequence (Earley.string "=" "=")
                         (Earley.sequence
                            (Earley.apply List.rev
                               (Earley.fixpoint []
                                  (Earley.apply (fun x  -> fun y  -> x :: y)
                                     string_litteral))) post_item_attributes
                            (fun ls  ->
                               fun a  ->
                                 fun _  ->
                                   fun ty  ->
                                     fun _  ->
                                       fun n  ->
                                         let (_loc_n,n) = n in
                                         fun _default_0  ->
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let l = List.length ls in
                                                   if (l < 1) || (l > 3)
                                                   then give_up ();
                                                   loc_sig _loc
                                                     (psig_value
                                                        ~attributes:(
                                                        attach_attrib _loc a)
                                                        _loc
                                                        (id_loc n _loc_n) ty
                                                        ls)))))));
           Earley.apply_position
             (fun td  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        loc_sig _loc (Psig_type (List.map snd td)))
             type_definition;
           Earley.sequence_position exception_declaration
             post_item_attributes
             (fun ((name,ed,_loc') as _default_0)  ->
                fun a  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          loc_sig _loc
                            (Psig_exception
                               (Te.decl ~attrs:(attach_attrib _loc' a)
                                  ~loc:_loc' ~args:ed name)));
           Earley.fsequence_position
             (Earley.apply_position
                (fun _default_0  ->
                   fun __loc__start__buf  ->
                     fun __loc__start__pos  ->
                       fun __loc__end__buf  ->
                         fun __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           attach_sig _loc) module_kw)
             (Earley.fsequence rec_kw
                (Earley.fsequence
                   (Earley.apply_position
                      (fun x  ->
                         fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  -> ((locate str pos str' pos'), x))
                      module_name)
                   (Earley.fsequence (Earley.string ":" ":")
                      (Earley.fsequence module_type
                         (Earley.sequence
                            (Earley.apply_position
                               (fun x  ->
                                  fun str  ->
                                    fun pos  ->
                                      fun str'  ->
                                        fun pos'  ->
                                          ((locate str pos str' pos'), x))
                               post_item_attributes)
                            (Earley.apply List.rev
                               (Earley.fixpoint []
                                  (Earley.apply (fun x  -> fun y  -> x :: y)
                                     (Earley.fsequence_position and_kw
                                        (Earley.fsequence module_name
                                           (Earley.fsequence
                                              (Earley.string ":" ":")
                                              (Earley.sequence module_type
                                                 post_item_attributes
                                                 (fun mt  ->
                                                    fun a  ->
                                                      fun _  ->
                                                        fun mn  ->
                                                          fun _default_0  ->
                                                            fun
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
                                                                    module_declaration
                                                                    ~attributes:(
                                                                    attach_attrib
                                                                    _loc a)
                                                                    _loc mn
                                                                    mt))))))))
                            (fun a  ->
                               let (_loc_a,a) = a in
                               fun ms  ->
                                 fun mt  ->
                                   fun _  ->
                                     fun mn  ->
                                       let (_loc_mn,mn) = mn in
                                       fun _default_0  ->
                                         fun _default_1  ->
                                           fun __loc__start__buf  ->
                                             fun __loc__start__pos  ->
                                               fun __loc__end__buf  ->
                                                 fun __loc__end__pos  ->
                                                   let _loc =
                                                     locate __loc__start__buf
                                                       __loc__start__pos
                                                       __loc__end__buf
                                                       __loc__end__pos in
                                                   let loc_first =
                                                     merge2 _loc_mn _loc_a in
                                                   let m =
                                                     module_declaration
                                                       ~attributes:(attach_attrib
                                                                    loc_first
                                                                    a)
                                                       loc_first mn mt in
                                                   loc_sig _loc
                                                     (Psig_recmodule (m ::
                                                        ms))))))));
           Earley.sequence_position
             (Earley.apply_position
                (fun _default_0  ->
                   fun __loc__start__buf  ->
                     fun __loc__start__pos  ->
                       fun __loc__end__buf  ->
                         fun __loc__end__pos  ->
                           let _loc =
                             locate __loc__start__buf __loc__start__pos
                               __loc__end__buf __loc__end__pos in
                           attach_sig _loc) module_kw)
             (Earley.alternatives
                [Earley.fsequence_position module_name
                   (Earley.fsequence
                      (Earley.apply List.rev
                         (Earley.fixpoint []
                            (Earley.apply (fun x  -> fun y  -> x :: y)
                               (Earley.fsequence_position
                                  (Earley.string "(" "(")
                                  (Earley.fsequence module_name
                                     (Earley.sequence
                                        (Earley.option None
                                           (Earley.apply (fun x  -> Some x)
                                              (Earley.sequence
                                                 (Earley.string ":" ":")
                                                 module_type
                                                 (fun _  -> fun mt  -> mt))))
                                        (Earley.string ")" ")")
                                        (fun mt  ->
                                           fun _  ->
                                             fun mn  ->
                                               fun _  ->
                                                 fun __loc__start__buf  ->
                                                   fun __loc__start__pos  ->
                                                     fun __loc__end__buf  ->
                                                       fun __loc__end__pos 
                                                         ->
                                                         let _loc =
                                                           locate
                                                             __loc__start__buf
                                                             __loc__start__pos
                                                             __loc__end__buf
                                                             __loc__end__pos in
                                                         (mn, mt, _loc))))))))
                      (Earley.fsequence (Earley.string ":" ":")
                         (Earley.sequence
                            (Earley.apply_position
                               (fun x  ->
                                  fun str  ->
                                    fun pos  ->
                                      fun str'  ->
                                        fun pos'  ->
                                          ((locate str pos str' pos'), x))
                               module_type) post_item_attributes
                            (fun mt  ->
                               let (_loc_mt,mt) = mt in
                               fun a  ->
                                 fun _  ->
                                   fun l  ->
                                     fun mn  ->
                                       fun __loc__start__buf  ->
                                         fun __loc__start__pos  ->
                                           fun __loc__end__buf  ->
                                             fun __loc__end__pos  ->
                                               let _loc =
                                                 locate __loc__start__buf
                                                   __loc__start__pos
                                                   __loc__end__buf
                                                   __loc__end__pos in
                                               let mt =
                                                 List.fold_left
                                                   (fun acc  ->
                                                      fun (mn,mt,_loc)  ->
                                                        mtyp_loc
                                                          (merge2 _loc
                                                             _loc_mt)
                                                          (Pmty_functor
                                                             (mn, mt, acc)))
                                                   mt (List.rev l) in
                                               Psig_module
                                                 (module_declaration
                                                    ~attributes:(attach_attrib
                                                                   _loc a)
                                                    _loc mn mt)))));
                Earley.fsequence_position type_kw
                  (Earley.fsequence
                     (Earley.apply_position
                        (fun x  ->
                           fun str  ->
                             fun pos  ->
                               fun str'  ->
                                 fun pos'  -> ((locate str pos str' pos'), x))
                        modtype_name)
                     (Earley.sequence
                        (Earley.option None
                           (Earley.apply (fun x  -> Some x)
                              (Earley.sequence (Earley.string "=" "=")
                                 module_type (fun _  -> fun mt  -> mt))))
                        post_item_attributes
                        (fun mt  ->
                           fun a  ->
                             fun mn  ->
                               let (_loc_mn,mn) = mn in
                               fun _default_0  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         Psig_modtype
                                           {
                                             pmtd_name = (id_loc mn _loc_mn);
                                             pmtd_type = mt;
                                             pmtd_attributes =
                                               (attach_attrib _loc a);
                                             pmtd_loc = _loc
                                           })))])
             (fun _default_0  ->
                fun r  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          loc_sig _loc r);
           Earley.fsequence_position open_kw
             (Earley.fsequence override_flag
                (Earley.sequence
                   (Earley.apply_position
                      (fun x  ->
                         fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  -> ((locate str pos str' pos'), x))
                      module_path) post_item_attributes
                   (fun m  ->
                      let (_loc_m,m) = m in
                      fun a  ->
                        fun o  ->
                          fun _default_0  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    loc_sig _loc
                                      (Psig_open
                                         {
                                           popen_lid = (id_loc m _loc_m);
                                           popen_override = o;
                                           popen_loc = _loc;
                                           popen_attributes =
                                             (attach_attrib _loc a)
                                         }))));
           Earley.fsequence_position include_kw
             (Earley.sequence module_type post_item_attributes
                (fun me  ->
                   fun a  ->
                     fun _default_0  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               loc_sig _loc
                                 (Psig_include
                                    {
                                      pincl_mod = me;
                                      pincl_loc = _loc;
                                      pincl_attributes =
                                        (attach_attrib _loc a)
                                    })));
           Earley.sequence_position class_kw
             (Earley.alternatives
                [Earley.apply (fun ctd  -> Psig_class_type ctd)
                   classtype_definition;
                Earley.apply (fun cs  -> Psig_class cs) class_specification])
             (fun _default_0  ->
                fun r  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          loc_sig _loc r);
           Earley.fsequence_position
             (Earley.ignore_next_blank (Earley.char '$' '$'))
             (Earley.sequence (Earley.ignore_next_blank expression)
                (Earley.char '$' '$')
                (fun e  ->
                   fun _  ->
                     fun dol  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
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
        (Earley.alternatives
           [Earley.apply_position
              (fun e  ->
                 fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         (attach_sig _loc) @ e)
              (alternatives extra_signature);
           Earley.sequence_position signature_item_base
             (Earley.option None
                (Earley.apply (fun x  -> Some x) double_semi_col))
             (fun s  ->
                fun _  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos in
                          (attach_sig _loc) @ [s])])
    exception Top_Exit
    let top_phrase = Earley.declare_grammar "top_phrase"
    let _ =
      Earley.set_grammar top_phrase
        (Earley.alternatives
           [Earley.fsequence
              (Earley.option None
                 (Earley.apply (fun x  -> Some x) (Earley.char ';' ';')))
              (Earley.sequence
                 (Earley.apply List.rev
                    (Earley.fixpoint1 []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          structure_item_base))) double_semi_col
                 (fun l  -> fun _default_0  -> fun _default_1  -> Ptop_def l));
           Earley.sequence
             (Earley.option None
                (Earley.apply (fun x  -> Some x) (Earley.char ';' ';')))
             (Earley.eof ()) (fun _default_0  -> fun _  -> raise Top_Exit)])
  end
