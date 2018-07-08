open Input
open Earley
open Charset
open Ast_helper
open Asttypes
open Parsetree
open Longident
open Pa_ast
open Pa_lexing
open Helper
include Pa_ocaml_prelude
module Make(Initial:Extension) =
  struct
    include Initial
    let ouident = uident 
    let uident = Earley.declare_grammar "uident" 
    let _ =
      Earley.set_grammar uident
        (Earley.alternatives
           [Earley.fsequence (Earley.string "$uid:" "$uid:")
              (Earley.fsequence expression
                 (Earley.fsequence (Earley.no_blank_test ())
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun _  ->
                                    fun e  ->
                                      fun _  ->
                                        Quote.string_antiquotation _loc e)
                       (Earley.char '$' '$'))));
           ouident])
      
    let olident = lident 
    let lident = Earley.declare_grammar "lident" 
    let _ =
      Earley.set_grammar lident
        (Earley.alternatives
           [Earley.fsequence (Earley.string "$lid:" "$lid:")
              (Earley.fsequence expression
                 (Earley.fsequence (Earley.no_blank_test ())
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun _  ->
                                    fun e  ->
                                      fun _  ->
                                        Quote.string_antiquotation _loc e)
                       (Earley.char '$' '$'))));
           olident])
      
    let oident = ident 
    let ident = Earley.declare_grammar "ident" 
    let _ =
      Earley.set_grammar ident
        (Earley.alternatives
           [Earley.fsequence (Earley.string "$ident:" "$ident:")
              (Earley.fsequence expression
                 (Earley.fsequence (Earley.no_blank_test ())
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun _  ->
                                    fun e  ->
                                      fun _  ->
                                        Quote.string_antiquotation _loc e)
                       (Earley.char '$' '$'))));
           oident])
      
    let mk_unary_op loc name loc_name arg =
      match (name, (arg.pexp_desc)) with
      | ("-",Pexp_constant (Pconst_integer (n,o))) ->
          Exp.constant ~loc (Const.integer ?suffix:o ("-" ^ n))
      | (("-"|"-."),Pexp_constant (Pconst_float (f,o))) ->
          Exp.constant ~loc (Const.float ?suffix:o ("-" ^ f))
      | ("+",Pexp_constant (Pconst_integer _))
        |(("+"|"+."),Pexp_constant (Pconst_float _)) ->
          Exp.mk ~loc arg.pexp_desc
      | (("-"|"-."|"+"|"+."),_) ->
          let lid = id_loc (Lident ("~" ^ name)) loc_name  in
          let fn = Exp.ident ~loc:loc_name lid  in
          Exp.apply ~loc fn [(nolabel, arg)]
      | _ ->
          let lid = id_loc (Lident name) loc_name  in
          let fn = Exp.ident ~loc:loc_name lid  in
          Exp.apply ~loc fn [(nolabel, arg)]
      
    let mk_binary_op loc e' op loc_op e =
      if op = "::"
      then
        let lid = id_loc (Lident "::") loc_op  in
        Exp.construct ~loc lid (Some (Exp.tuple ~loc:(ghost loc) [e'; e]))
      else
        (let id = Exp.ident ~loc:loc_op (id_loc (Lident op) loc_op)  in
         Exp.apply ~loc id [(nolabel, e'); (nolabel, e)])
      
    let wrap_type_annotation loc types core_type body =
      let exp = Exp.constraint_ ~loc body core_type  in
      let exp =
        List.fold_right (fun ty  -> fun exp  -> Exp.newtype ~loc ty exp)
          types exp
         in
      (exp,
        (Typ.poly ~loc:(ghost loc) types
           (Typ.varify_constructors types core_type)))
      
    type tree =
      | Node of tree * tree 
      | Leaf of string 
    let string_of_tree (t : tree) =
      (let b = Buffer.create 101  in
       let rec fn =
         function
         | Leaf s -> Buffer.add_string b s
         | Node (a,b) -> (fn a; fn b)  in
       fn t; Buffer.contents b : string)
      
    let label_name = lident 
    let ty_label = Earley.declare_grammar "ty_label" 
    let _ =
      Earley.set_grammar ty_label
        (Earley.fsequence (Earley.char '~' '~')
           (Earley.fsequence (Earley.no_blank_test ())
              (Earley.fsequence lident
                 (Earley.apply
                    (fun _  -> fun s  -> fun _  -> fun _  -> labelled s)
                    (Earley.char ':' ':')))))
      
    let ty_opt_label = Earley.declare_grammar "ty_opt_label" 
    let _ =
      Earley.set_grammar ty_opt_label
        (Earley.fsequence (Earley.char '?' '?')
           (Earley.fsequence (Earley.no_blank_test ())
              (Earley.fsequence lident
                 (Earley.apply
                    (fun _  -> fun s  -> fun _  -> fun _  -> optional s)
                    (Earley.char ':' ':')))))
      
    let maybe_opt_label = Earley.declare_grammar "maybe_opt_label" 
    let _ =
      Earley.set_grammar maybe_opt_label
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x) (Earley.string "?" "?")))
           (Earley.apply
              (fun ln  ->
                 fun o  -> if o = None then labelled ln else optional ln)
              label_name))
      
    let list_antiquotation _loc e =
      let open Quote in
        let generic_antiquote e =
          function | Quote_loc  -> e | _ -> failwith "invalid antiquotation"
           in
        make_list_antiquotation _loc Quote_loc (generic_antiquote e)
      
    let operator_name =
      alternatives ((prefix_symbol Prefix) ::
        (List.map infix_symbol infix_prios))
      
    let value_name = Earley.declare_grammar "value_name" 
    let _ =
      Earley.set_grammar value_name
        (Earley.alternatives
           [Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence operator_name
                 (Earley.apply (fun _  -> fun op  -> fun _  -> op)
                    (Earley.char ')' ')')));
           lident])
      
    let constr_name = uident 
    let tag_name = Earley.declare_grammar "tag_name" 
    let _ =
      Earley.set_grammar tag_name
        (Earley.fsequence (Earley.string "`" "`")
           (Earley.apply (fun c  -> fun _  -> c) ident))
      
    let typeconstr_name = lident 
    let field_name = lident 
    let smodule_name = uident 
    let module_name = Earley.declare_grammar "module_name" 
    let _ =
      Earley.set_grammar module_name
        (Earley.apply_position
           (fun __loc__start__buf  ->
              fun __loc__start__pos  ->
                fun __loc__end__buf  ->
                  fun __loc__end__pos  ->
                    let _loc =
                      locate __loc__start__buf __loc__start__pos
                        __loc__end__buf __loc__end__pos
                       in
                    fun u  -> id_loc u _loc) uident)
      
    let modtype_name = ident 
    let class_name = lident 
    let inst_var_name = lident 
    let method_name = Earley.declare_grammar "method_name" 
    let _ =
      Earley.set_grammar method_name
        (Earley.apply_position
           (fun __loc__start__buf  ->
              fun __loc__start__pos  ->
                fun __loc__end__buf  ->
                  fun __loc__end__pos  ->
                    let _loc =
                      locate __loc__start__buf __loc__start__pos
                        __loc__end__buf __loc__end__pos
                       in
                    fun id  -> id_loc id _loc) lident)
      
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
             ((Earley.fsequence (Earley.string "." ".")
                 (Earley.apply
                    (fun m  -> fun _  -> fun acc  -> Ldot (acc, m))
                    smodule_name)) ::
             ((if allow_app
               then
                 [Earley.fsequence (Earley.string "(" "(")
                    (Earley.fsequence (module_path_gen true)
                       (Earley.apply
                          (fun _  ->
                             fun m'  -> fun _  -> fun a  -> Lapply (a, m'))
                          (Earley.string ")" ")")))]
               else []) @ [])))
      
    let _ =
      set_module_path_suit
        (fun allow_app  ->
           Earley.alternatives
             [Earley.apply (fun _  -> fun acc  -> acc) (Earley.empty ());
             Earley.fsequence (module_path_suit_aux allow_app)
               (Earley.apply (fun g  -> fun f  -> fun acc  -> g (f acc))
                  (module_path_suit allow_app))])
      
    let _ =
      set_module_path_gen
        (fun allow_app  ->
           Earley.fsequence smodule_name
             (Earley.apply (fun s  -> fun m  -> s (Lident m))
                (module_path_suit allow_app)))
      
    let module_path = module_path_gen false 
    let extended_module_path = module_path_gen true 
    let _ =
      set_grammar value_path
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun vn  ->
                 fun mp  ->
                   match mp with
                   | None  -> Lident vn
                   | Some p -> Ldot (p, vn)) value_name))
      
    let constr = Earley.declare_grammar "constr" 
    let _ =
      Earley.set_grammar constr
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun cn  ->
                 fun mp  ->
                   match mp with
                   | None  -> Lident cn
                   | Some p -> Ldot (p, cn)) constr_name))
      
    let typeconstr = Earley.declare_grammar "typeconstr" 
    let _ =
      Earley.set_grammar typeconstr
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence extended_module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun tcn  ->
                 fun mp  ->
                   match mp with
                   | None  -> Lident tcn
                   | Some p -> Ldot (p, tcn)) typeconstr_name))
      
    let field = Earley.declare_grammar "field" 
    let _ =
      Earley.set_grammar field
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun fn  ->
                 fun mp  ->
                   match mp with
                   | None  -> Lident fn
                   | Some p -> Ldot (p, fn)) field_name))
      
    let class_path = Earley.declare_grammar "class_path" 
    let _ =
      Earley.set_grammar class_path
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun cn  ->
                 fun mp  ->
                   match mp with
                   | None  -> Lident cn
                   | Some p -> Ldot (p, cn)) class_name))
      
    let modtype_path = Earley.declare_grammar "modtype_path" 
    let _ =
      Earley.set_grammar modtype_path
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence extended_module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun mtn  ->
                 fun mp  ->
                   match mp with
                   | None  -> Lident mtn
                   | Some p -> Ldot (p, mtn)) modtype_name))
      
    let classtype_path = Earley.declare_grammar "classtype_path" 
    let _ =
      Earley.set_grammar classtype_path
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence extended_module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun cn  ->
                 fun mp  ->
                   match mp with
                   | None  -> Lident cn
                   | Some p -> Ldot (p, cn)) class_name))
      
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
        (Earley.fsequence ident
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun l  ->
                         fun id  -> id_loc (String.concat "." (id :: l)) _loc)
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.fsequence (Earley.char '.' '.')
                          (Earley.apply (fun id  -> fun _  -> id) ident)))))))
      
    let payload = Earley.declare_grammar "payload" 
    let _ =
      Earley.set_grammar payload
        (Earley.alternatives
           [Earley.fsequence (Earley.char '?' '?')
              (Earley.fsequence pattern
                 (Earley.apply (fun e  -> fun p  -> fun _  -> PPat (p, e))
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x)
                          (Earley.fsequence when_kw
                             (Earley.apply (fun e  -> fun _  -> e) expression))))));
           Earley.apply (fun s  -> PStr s) structure;
           Earley.fsequence (Earley.char ':' ':')
             (Earley.apply (fun t  -> fun _  -> PTyp t) typexpr)])
      
    let attribute = Earley.declare_grammar "attribute" 
    let _ =
      Earley.set_grammar attribute
        (Earley.fsequence (Earley.string "[@" "[@")
           (Earley.fsequence attr_id
              (Earley.fsequence payload
                 (Earley.apply
                    (fun _  -> fun p  -> fun id  -> fun _  -> (id, p))
                    (Earley.char ']' ']')))))
      
    let attributes = Earley.declare_grammar "attributes" 
    let _ =
      Earley.set_grammar attributes
        (Earley.apply List.rev
           (Earley.fixpoint []
              (Earley.apply (fun x  -> fun y  -> x :: y) attribute)))
      
    let ext_attributes = Earley.declare_grammar "ext_attributes" 
    let _ =
      Earley.set_grammar ext_attributes
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence (Earley.char '%' '%')
                    (Earley.apply (fun a  -> fun _  -> a) attribute))))
           (Earley.apply (fun l  -> fun a  -> (a, l)) attributes))
      
    let post_item_attributes = Earley.declare_grammar "post_item_attributes" 
    let _ =
      Earley.set_grammar post_item_attributes
        (Earley.apply List.rev
           (Earley.fixpoint []
              (Earley.apply (fun x  -> fun y  -> x :: y)
                 (Earley.fsequence (Earley.string "[@@" "[@@")
                    (Earley.fsequence attr_id
                       (Earley.fsequence payload
                          (Earley.apply
                             (fun _  ->
                                fun p  -> fun id  -> fun _  -> (id, p))
                             (Earley.char ']' ']'))))))))
      
    let floating_attribute = Earley.declare_grammar "floating_attribute" 
    let _ =
      Earley.set_grammar floating_attribute
        (Earley.fsequence (Earley.string "[@@@" "[@@@")
           (Earley.fsequence attr_id
              (Earley.fsequence payload
                 (Earley.apply
                    (fun _  -> fun p  -> fun id  -> fun _  -> (id, p))
                    (Earley.char ']' ']')))))
      
    let extension = Earley.declare_grammar "extension" 
    let _ =
      Earley.set_grammar extension
        (Earley.fsequence (Earley.string "[%" "[%")
           (Earley.fsequence attr_id
              (Earley.fsequence payload
                 (Earley.apply
                    (fun _  -> fun p  -> fun id  -> fun _  -> (id, p))
                    (Earley.char ']' ']')))))
      
    let floating_extension = Earley.declare_grammar "floating_extension" 
    let _ =
      Earley.set_grammar floating_extension
        (Earley.fsequence (Earley.string "[%%" "[%%")
           (Earley.fsequence attr_id
              (Earley.fsequence payload
                 (Earley.apply
                    (fun _  -> fun p  -> fun id  -> fun _  -> (id, p))
                    (Earley.char ']' ']')))))
      
    let only_poly_typexpr = Earley.declare_grammar "only_poly_typexpr" 
    let _ =
      Earley.set_grammar only_poly_typexpr
        (Earley.fsequence
           (Earley.apply List.rev
              (Earley.fixpoint1 []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.fsequence (Earley.char '\'' '\'')
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun id  -> fun _  -> id_loc id _loc) ident)))))
           (Earley.fsequence (Earley.char '.' '.')
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun te  ->
                            fun _  -> fun ids  -> Typ.poly ~loc:_loc ids te)
                 typexpr)))
      
    let poly_typexpr = Earley.declare_grammar "poly_typexpr" 
    let _ =
      Earley.set_grammar poly_typexpr
        (Earley.alternatives
           [typexpr;
           Earley.fsequence
             (Earley.apply List.rev
                (Earley.fixpoint1 []
                   (Earley.apply (fun x  -> fun y  -> x :: y)
                      (Earley.fsequence (Earley.char '\'' '\'')
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun id  -> fun _  -> id_loc id _loc)
                            ident)))))
             (Earley.fsequence (Earley.char '.' '.')
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun te  ->
                              fun _  -> fun ids  -> Typ.poly ~loc:_loc ids te)
                   typexpr))])
      
    let poly_syntax_typexpr = Earley.declare_grammar "poly_syntax_typexpr" 
    let _ =
      Earley.set_grammar poly_syntax_typexpr
        (Earley.fsequence type_kw
           (Earley.fsequence
              (Earley.apply List.rev
                 (Earley.fixpoint1 []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.apply
                          (fun id  ->
                             let (_loc_id,id) = id  in id_loc id _loc_id)
                          (Earley.apply_position
                             (fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      fun x  ->
                                        ((locate str pos str' pos'), x))
                             typeconstr_name)))))
              (Earley.fsequence (Earley.char '.' '.')
                 (Earley.apply
                    (fun te  ->
                       fun _  -> fun ids  -> fun _default_0  -> (ids, te))
                    typexpr))))
      
    let method_type = Earley.declare_grammar "method_type" 
    let _ =
      Earley.set_grammar method_type
        (Earley.fsequence method_name
           (Earley.fsequence (Earley.char ':' ':')
              (Earley.apply (fun pte  -> fun _  -> fun mn  -> (mn, [], pte))
                 poly_typexpr)))
      
    let tag_spec = Earley.declare_grammar "tag_spec" 
    let _ =
      Earley.set_grammar tag_spec
        (Earley.alternatives
           [Earley.apply (fun te  -> Rinherit te) typexpr;
           Earley.fsequence tag_name
             (Earley.apply
                (fun te  ->
                   fun tn  ->
                     let (amp,t) =
                       match te with
                       | None  -> (true, [])
                       | Some (amp,l) -> ((amp <> None), [l])  in
                     Rtag (tn, [], amp, t))
                (Earley.option None
                   (Earley.apply (fun x  -> Some x)
                      (Earley.fsequence of_kw
                         (Earley.fsequence
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.char '&' '&')))
                            (Earley.apply
                               (fun _default_0  ->
                                  fun _default_1  ->
                                    fun _  -> (_default_1, _default_0))
                               typexpr))))))])
      
    let tag_spec_first = Earley.declare_grammar "tag_spec_first" 
    let _ =
      Earley.set_grammar tag_spec_first
        (Earley.alternatives
           [Earley.fsequence
              (Earley.option None (Earley.apply (fun x  -> Some x) typexpr))
              (Earley.fsequence (Earley.char '|' '|')
                 (Earley.apply
                    (fun ts  ->
                       fun _  ->
                         fun te  ->
                           match te with
                           | None  -> [ts]
                           | Some te -> [Rinherit te; ts]) tag_spec));
           Earley.fsequence tag_name
             (Earley.apply
                (fun te  ->
                   fun tn  ->
                     let (amp,t) =
                       match te with
                       | None  -> (true, [])
                       | Some (amp,l) -> ((amp <> None), [l])  in
                     [Rtag (tn, [], amp, t)])
                (Earley.option None
                   (Earley.apply (fun x  -> Some x)
                      (Earley.fsequence of_kw
                         (Earley.fsequence
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.char '&' '&')))
                            (Earley.apply
                               (fun _default_0  ->
                                  fun _default_1  ->
                                    fun _  -> (_default_1, _default_0))
                               typexpr))))))])
      
    let tag_spec_full = Earley.declare_grammar "tag_spec_full" 
    let _ =
      Earley.set_grammar tag_spec_full
        (Earley.alternatives
           [Earley.apply (fun te  -> Rinherit te) typexpr;
           Earley.fsequence tag_name
             (Earley.apply
                (fun ((amp,tes) as _default_0)  ->
                   fun tn  -> Rtag (tn, [], amp, tes))
                (Earley.option (true, [])
                   (Earley.fsequence of_kw
                      (Earley.fsequence
                         (Earley.option None
                            (Earley.apply (fun x  -> Some x)
                               (Earley.char '&' '&')))
                         (Earley.fsequence typexpr
                            (Earley.apply
                               (fun tes  ->
                                  fun te  ->
                                    fun amp  ->
                                      fun _default_0  ->
                                        ((amp <> None), (te :: tes)))
                               (Earley.apply List.rev
                                  (Earley.fixpoint []
                                     (Earley.apply
                                        (fun x  -> fun y  -> x :: y)
                                        (Earley.fsequence
                                           (Earley.char '&' '&')
                                           (Earley.apply
                                              (fun te  -> fun _  -> te)
                                              typexpr)))))))))))])
      
    let polymorphic_variant_type =
      Earley.declare_grammar "polymorphic_variant_type" 
    let _ =
      Earley.set_grammar polymorphic_variant_type
        (Earley.alternatives
           [Earley.fsequence (Earley.string "[<" "[<")
              (Earley.fsequence
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x) (Earley.char '|' '|')))
                 (Earley.fsequence tag_spec_full
                    (Earley.fsequence
                       (Earley.apply List.rev
                          (Earley.fixpoint []
                             (Earley.apply (fun x  -> fun y  -> x :: y)
                                (Earley.fsequence (Earley.char '|' '|')
                                   (Earley.apply (fun tsf  -> fun _  -> tsf)
                                      tag_spec_full)))))
                       (Earley.fsequence
                          (Earley.option []
                             (Earley.fsequence (Earley.char '>' '>')
                                (Earley.apply (fun tns  -> fun _  -> tns)
                                   (Earley.apply List.rev
                                      (Earley.fixpoint1 []
                                         (Earley.apply
                                            (fun x  -> fun y  -> x :: y)
                                            tag_name))))))
                          (Earley.apply_position
                             (fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos
                                         in
                                      fun _  ->
                                        fun tns  ->
                                          fun tfss  ->
                                            fun tfs  ->
                                              fun _default_0  ->
                                                fun _  ->
                                                  Typ.variant ~loc:_loc (tfs
                                                    :: tfss) Closed
                                                    (Some tns))
                             (Earley.char ']' ']'))))));
           Earley.fsequence (Earley.char '[' '[')
             (Earley.fsequence tag_spec_first
                (Earley.fsequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            (Earley.fsequence (Earley.char '|' '|')
                               (Earley.apply (fun ts  -> fun _  -> ts)
                                  tag_spec)))))
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun _  ->
                                 fun tss  ->
                                   fun tsf  ->
                                     fun _  ->
                                       Typ.variant ~loc:_loc (tsf @ tss)
                                         Closed None) (Earley.char ']' ']'))));
           Earley.fsequence (Earley.string "[>" "[>")
             (Earley.fsequence
                (Earley.option None
                   (Earley.apply (fun x  -> Some x) tag_spec))
                (Earley.fsequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            (Earley.fsequence (Earley.char '|' '|')
                               (Earley.apply (fun ts  -> fun _  -> ts)
                                  tag_spec)))))
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun _  ->
                                 fun tss  ->
                                   fun ts  ->
                                     fun _  ->
                                       let tss =
                                         match ts with
                                         | None  -> tss
                                         | Some ts -> ts :: tss  in
                                       Typ.variant ~loc:_loc tss Open None)
                      (Earley.char ']' ']'))))] : core_type grammar)
      
    let package_constraint = Earley.declare_grammar "package_constraint" 
    let _ =
      Earley.set_grammar package_constraint
        (Earley.fsequence type_kw
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 typeconstr)
              (Earley.fsequence (Earley.char '=' '=')
                 (Earley.apply
                    (fun te  ->
                       fun _  ->
                         fun tc  ->
                           let (_loc_tc,tc) = tc  in
                           fun _default_0  ->
                             let tc = id_loc tc _loc_tc  in (tc, te)) typexpr))))
      
    let package_type = Earley.declare_grammar "package_type" 
    let _ =
      Earley.set_grammar package_type
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              modtype_path)
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun cs  ->
                         fun mtp  ->
                           let (_loc_mtp,mtp) = mtp  in
                           Typ.package ~loc:_loc (id_loc mtp _loc_mtp) cs)
              (Earley.option []
                 (Earley.fsequence with_kw
                    (Earley.fsequence package_constraint
                       (Earley.apply
                          (fun pcs  ->
                             fun pc  -> fun _default_0  -> pc :: pcs)
                          (Earley.apply List.rev
                             (Earley.fixpoint []
                                (Earley.apply (fun x  -> fun y  -> x :: y)
                                   (Earley.fsequence and_kw
                                      (Earley.apply
                                         (fun _default_0  ->
                                            fun _  -> _default_0)
                                         package_constraint)))))))))))
      
    let opt_present = Earley.declare_grammar "opt_present" 
    let _ =
      Earley.set_grammar opt_present
        (Earley.alternatives
           [Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence (Earley.string "[>" "[>")
             (Earley.fsequence
                (Earley.apply List.rev
                   (Earley.fixpoint1 []
                      (Earley.apply (fun x  -> fun y  -> x :: y) tag_name)))
                (Earley.apply (fun _  -> fun l  -> fun _  -> l)
                   (Earley.string "]" "]")))])
      
    let mkoption loc d =
      let loc = ghost loc  in
      Typ.constr ~loc (id_loc (Ldot ((Lident "*predef*"), "option")) loc) [d] 
    let extra_types_grammar lvl =
      alternatives (List.map (fun g  -> g lvl) extra_types) 
    let op_cl =
      Earley.alternatives
        [Earley.apply (fun _  -> Closed) (Earley.empty ());
        Earley.apply (fun d  -> Open) (Earley.string ".." "..")]
      
    let _ =
      set_typexpr_lvl
        ([(((fun _  -> true)),
            (Earley.fsequence (Earley.char '$' '$')
               (Earley.fsequence (Earley.no_blank_test ())
                  (Earley.fsequence
                     (Earley.option "type"
                        (Earley.fsequence
                           (EarleyStr.regexp ~name:"[a-z]+" "[a-z]+"
                              (fun groupe  -> groupe 0))
                           (Earley.fsequence (Earley.no_blank_test ())
                              (Earley.apply
                                 (fun _  ->
                                    fun _  -> fun _default_0  -> _default_0)
                                 (Earley.char ':' ':')))))
                     (Earley.fsequence expression
                        (Earley.fsequence (Earley.no_blank_test ())
                           (Earley.apply_position
                              (fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos
                                          in
                                       fun _  ->
                                         fun _  ->
                                           fun e  ->
                                             fun aq  ->
                                               fun _  ->
                                                 fun _  ->
                                                   let open Quote in
                                                     let e_loc =
                                                       exp_ident _loc "_loc"
                                                        in
                                                     let generic_antiquote e
                                                       =
                                                       function
                                                       | Quote_ptyp  -> e
                                                       | _ ->
                                                           failwith
                                                             "invalid antiquotation"
                                                        in
                                                     let f =
                                                       match aq with
                                                       | "type" ->
                                                           generic_antiquote
                                                             e
                                                       | "tuple" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "typ_tuple")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | _ -> give_up ()  in
                                                     Quote.ptyp_antiquotation
                                                       _loc f)
                              (Earley.char '$' '$'))))))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.string "'" "'")
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun id  -> fun _  -> Typ.var ~loc:_loc id) ident)));
         (((fun _  -> true)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun _default_0  -> Typ.any ~loc:_loc ()) joker_kw));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence module_kw
                 (Earley.fsequence package_type
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun pt  ->
                                    fun _default_0  ->
                                      fun _  -> loc_typ _loc pt.ptyp_desc)
                       (Earley.char ')' ')'))))));
         (((fun (allow_par,lvl)  -> allow_par)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence typexpr
                 (Earley.fsequence
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             attribute)))
                    (Earley.apply
                       (fun _  ->
                          fun at  ->
                            fun te  ->
                              fun _  -> { te with ptyp_attributes = at })
                       (Earley.char ')' ')'))))));
         (((fun (allow_par,lvl)  -> lvl <= Arr)),
           (Earley.fsequence ty_opt_label
              (Earley.fsequence (typexpr_lvl ProdType)
                 (Earley.fsequence arrow_re
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun te'  ->
                                  fun _default_0  ->
                                    fun te  ->
                                      fun ln  ->
                                        Typ.arrow ~loc:_loc ln te te')
                       (typexpr_lvl Arr))))));
         (((fun (allow_par,lvl)  -> lvl <= Arr)),
           (Earley.fsequence label_name
              (Earley.fsequence (Earley.char ':' ':')
                 (Earley.fsequence (typexpr_lvl ProdType)
                    (Earley.fsequence arrow_re
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun te'  ->
                                     fun _default_0  ->
                                       fun te  ->
                                         fun _  ->
                                           fun ln  ->
                                             Typ.arrow ~loc:_loc
                                               (labelled ln) te te')
                          (typexpr_lvl Arr)))))));
         (((fun (allow_par,lvl)  -> lvl <= Arr)),
           (Earley.fsequence (typexpr_lvl ProdType)
              (Earley.fsequence arrow_re
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun te'  ->
                               fun _default_0  ->
                                 fun te  ->
                                   Typ.arrow ~loc:_loc nolabel te te')
                    (typexpr_lvl Arr)))));
         (((fun _  -> true)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun tc  ->
                         let (_loc_tc,tc) = tc  in
                         Typ.constr ~loc:_loc (id_loc tc _loc_tc) [])
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 typeconstr)));
         (((fun (allow_par,lvl)  -> lvl <= AppType)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence typexpr
                 (Earley.fsequence
                    (Earley.apply List.rev
                       (Earley.fixpoint1 []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             (Earley.fsequence (Earley.char ',' ',')
                                (Earley.apply (fun te  -> fun _  -> te)
                                   typexpr)))))
                    (Earley.fsequence (Earley.char ')' ')')
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun tc  ->
                                     let (_loc_tc,tc) = tc  in
                                     fun _  ->
                                       fun tes  ->
                                         fun te  ->
                                           fun _  ->
                                             Typ.constr ~loc:_loc
                                               (id_loc tc _loc_tc) (te ::
                                               tes))
                          (Earley.apply_position
                             (fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      fun x  ->
                                        ((locate str pos str' pos'), x))
                             typeconstr)))))));
         (((fun (allow_par,lvl)  -> lvl <= AppType)),
           (Earley.fsequence (typexpr_lvl AppType)
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun tc  ->
                            let (_loc_tc,tc) = tc  in
                            fun t  ->
                              Typ.constr ~loc:_loc (id_loc tc _loc_tc) [t])
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    typeconstr))));
         (((fun _  -> true)), polymorphic_variant_type);
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '<' '<')
              (Earley.fsequence op_cl
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _  ->
                               fun rv  ->
                                 fun _  -> Typ.object_ ~loc:_loc [] rv)
                    (Earley.char '>' '>')))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '<' '<')
              (Earley.fsequence (Earley.list1 method_type semi_col)
                 (Earley.fsequence
                    (Earley.option Closed
                       (Earley.fsequence semi_col
                          (Earley.apply
                             (fun _default_0  -> fun _  -> _default_0) op_cl)))
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun rv  ->
                                    fun mts  ->
                                      fun _  -> Typ.object_ ~loc:_loc mts rv)
                       (Earley.char '>' '>'))))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '#' '#')
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun cp  ->
                            let (_loc_cp,cp) = cp  in
                            fun _  ->
                              Typ.class_ ~loc:_loc (id_loc cp _loc_cp) [])
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    class_path))));
         (((fun (allow_par,lvl)  -> lvl <= DashType)),
           (Earley.fsequence (typexpr_lvl DashType)
              (Earley.fsequence (Earley.char '#' '#')
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun cp  ->
                               let (_loc_cp,cp) = cp  in
                               fun _  ->
                                 fun te  ->
                                   Typ.class_ ~loc:_loc (id_loc cp _loc_cp)
                                     [te])
                    (Earley.apply_position
                       (fun str  ->
                          fun pos  ->
                            fun str'  ->
                              fun pos'  ->
                                fun x  -> ((locate str pos str' pos'), x))
                       class_path)))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence typexpr
                 (Earley.fsequence
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             (Earley.fsequence (Earley.char ',' ',')
                                (Earley.apply (fun te  -> fun _  -> te)
                                   typexpr)))))
                    (Earley.fsequence (Earley.char ')' ')')
                       (Earley.fsequence (Earley.char '#' '#')
                          (Earley.apply_position
                             (fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos
                                         in
                                      fun cp  ->
                                        let (_loc_cp,cp) = cp  in
                                        fun _  ->
                                          fun _  ->
                                            fun tes  ->
                                              fun te  ->
                                                fun _  ->
                                                  Typ.class_ ~loc:_loc
                                                    (id_loc cp _loc_cp) (te
                                                    :: tes))
                             (Earley.apply_position
                                (fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         fun x  ->
                                           ((locate str pos str' pos'), x))
                                class_path))))))));
         (((fun (allow_par,lvl)  -> lvl <= ProdType)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun tes  -> Typ.tuple ~loc:_loc tes)
              (Earley.list2 (typexpr_lvl DashType)
                 (Earley.alternatives
                    [Earley.apply (fun _  -> ())
                       (Earley.string "\195\151" "\195\151");
                    Earley.apply (fun _  -> ()) (Earley.char '*' '*')]))));
         (((fun (allow_par,lvl)  -> lvl <= As)),
           (Earley.fsequence (typexpr_lvl As)
              (Earley.fsequence as_kw
                 (Earley.fsequence (Earley.char '\'' '\'')
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun id  ->
                                  fun _  ->
                                    fun _default_0  ->
                                      fun te  -> Typ.alias ~loc:_loc te id)
                       ident)))))],
          (fun (allow_par,lvl)  -> [extra_types_grammar lvl]))
      
    let type_param = Earley.declare_grammar "type_param" 
    let _ =
      Earley.set_grammar type_param
        (Earley.alternatives
           [Earley.fsequence opt_variance
              (Earley.apply
                 (fun j  ->
                    let (_loc_j,j) = j  in fun var  -> ((Joker _loc_j), var))
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    (Earley.char '_' '_')));
           Earley.fsequence opt_variance
             (Earley.apply
                (fun id  ->
                   let (_loc_id,id) = id  in
                   fun var  -> ((Name (id_loc id _loc_id)), var))
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   (Earley.fsequence (Earley.char '\'' '\'')
                      (Earley.apply (fun _default_0  -> fun _  -> _default_0)
                         ident))))])
      
    let type_params = Earley.declare_grammar "type_params" 
    let _ =
      Earley.set_grammar type_params
        (Earley.alternatives
           [Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence type_param
                 (Earley.fsequence
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             (Earley.fsequence (Earley.char ',' ',')
                                (Earley.apply (fun tp  -> fun _  -> tp)
                                   type_param)))))
                    (Earley.apply
                       (fun _  -> fun tps  -> fun tp  -> fun _  -> tp :: tps)
                       (Earley.char ')' ')'))));
           Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.apply (fun tp  -> [tp]) type_param])
      
    let type_equation = Earley.declare_grammar "type_equation" 
    let _ =
      Earley.set_grammar type_equation
        (Earley.fsequence (Earley.char '=' '=')
           (Earley.fsequence private_flag
              (Earley.apply (fun te  -> fun p  -> fun _  -> (p, te)) typexpr)))
      
    let type_constraint = Earley.declare_grammar "type_constraint" 
    let _ =
      Earley.set_grammar type_constraint
        (Earley.fsequence constraint_kw
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 (Earley.fsequence (Earley.char '\'' '\'')
                    (Earley.apply (fun _default_0  -> fun _  -> _default_0)
                       ident)))
              (Earley.fsequence (Earley.char '=' '=')
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun te  ->
                               fun _  ->
                                 fun id  ->
                                   let (_loc_id,id) = id  in
                                   fun _default_0  ->
                                     ((Typ.var ~loc:_loc_id id), te,
                                       (merge2 _loc_id _loc))) typexpr))))
      
    let constr_name2 = Earley.declare_grammar "constr_name2" 
    let _ =
      Earley.set_grammar constr_name2
        (Earley.alternatives
           [Earley.fsequence (Earley.char '(' '(')
              (Earley.apply (fun _  -> fun _  -> "()") (Earley.char ')' ')'));
           constr_name])
      
    let (bar,bar__set__grammar) = Earley.grammar_family "bar" 
    let _ =
      bar__set__grammar
        (fun with_bar  ->
           Earley.alternatives
             ((Earley.apply (fun _  -> ()) (Earley.char '|' '|')) ::
             ((if not with_bar
               then [Earley.apply (fun _  -> ()) (Earley.empty ())]
               else []) @ [])))
      
    let (constr_decl,constr_decl__set__grammar) =
      Earley.grammar_family "constr_decl" 
    let _ =
      constr_decl__set__grammar
        (fun with_bar  ->
           Earley.fsequence (bar with_bar)
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   constr_name2)
                (Earley.fsequence
                   (Earley.alternatives
                      [Earley.fsequence (Earley.char ':' ':')
                         (Earley.fsequence (Earley.char '{' '{')
                            (Earley.fsequence field_decl_list
                               (Earley.fsequence (Earley.char '}' '}')
                                  (Earley.fsequence arrow_re
                                     (Earley.apply
                                        (fun te  ->
                                           fun _default_0  ->
                                             fun _  ->
                                               fun fds  ->
                                                 fun _  ->
                                                   fun _  ->
                                                     ((Pcstr_record fds),
                                                       (Some te)))
                                        (typexpr_lvl (next_type_prio Arr)))))));
                      Earley.apply
                        (fun te  ->
                           let tes =
                             match te with
                             | None  -> []
                             | Some ({ ptyp_desc = Ptyp_tuple tes },false )
                                 -> tes
                             | Some (t,_) -> [t]  in
                           ((Pcstr_tuple tes), None))
                        (Earley.option None
                           (Earley.apply (fun x  -> Some x)
                              (Earley.fsequence of_kw
                                 (Earley.apply
                                    (fun _default_0  -> fun _  -> _default_0)
                                    (Earley.alternatives
                                       [Earley.apply (fun te  -> (te, false))
                                          typexpr_nopar;
                                       Earley.fsequence (Earley.char '(' '(')
                                         (Earley.fsequence typexpr
                                            (Earley.apply
                                               (fun _  ->
                                                  fun te  ->
                                                    fun _  -> (te, true))
                                               (Earley.char ')' ')')))])))));
                      Earley.fsequence of_kw
                        (Earley.fsequence (Earley.char '{' '{')
                           (Earley.fsequence field_decl_list
                              (Earley.apply
                                 (fun _  ->
                                    fun fds  ->
                                      fun _  ->
                                        fun _default_0  ->
                                          ((Pcstr_record fds), None))
                                 (Earley.char '}' '}'))));
                      Earley.fsequence (Earley.char ':' ':')
                        (Earley.fsequence
                           (Earley.option []
                              (Earley.fsequence
                                 (typexpr_lvl (next_type_prio ProdType))
                                 (Earley.fsequence
                                    (Earley.apply List.rev
                                       (Earley.fixpoint []
                                          (Earley.apply
                                             (fun x  -> fun y  -> x :: y)
                                             (Earley.fsequence
                                                (Earley.char '*' '*')
                                                (Earley.apply
                                                   (fun _default_0  ->
                                                      fun _  -> _default_0)
                                                   (typexpr_lvl
                                                      (next_type_prio
                                                         ProdType)))))))
                                    (Earley.apply
                                       (fun _default_0  ->
                                          fun tes  -> fun te  -> te :: tes)
                                       arrow_re))))
                           (Earley.apply
                              (fun te  ->
                                 fun tes  ->
                                   fun _  -> ((Pcstr_tuple tes), (Some te)))
                              (typexpr_lvl (next_type_prio Arr))))])
                   (Earley.apply
                      (fun a  ->
                         fun ((args,res) as _default_0)  ->
                           fun cn  ->
                             let (_loc_cn,cn) = cn  in
                             fun _default_1  ->
                               let name = id_loc cn _loc_cn  in
                               (name, args, res, a)) post_item_attributes))))
      
    [@@@ocaml.text " FIXME OCAML: the bar is included in position "]
    let (type_constr_decl,type_constr_decl__set__grammar) =
      Earley.grammar_family "type_constr_decl" 
    let _ =
      type_constr_decl__set__grammar
        (fun with_bar  ->
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ((name,args,res,a) as _default_0)  ->
                        Type.constructor ~attrs:(attach_attrib _loc a)
                          ~loc:_loc ~args ?res name) (constr_decl with_bar))
      
    let (type_constr_extn,type_constr_extn__set__grammar) =
      Earley.grammar_family "type_constr_extn" 
    let _ =
      type_constr_extn__set__grammar
        (fun with_bar  ->
           Earley.alternatives
             [Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x)) lident)
                (Earley.fsequence (Earley.char '=' '=')
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  ->
                                  fun x  -> ((locate str pos str' pos'), x))
                         constr)
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun a  ->
                                    fun cn  ->
                                      let (_loc_cn,cn) = cn  in
                                      fun _  ->
                                        fun li  ->
                                          let (_loc_li,li) = li  in
                                          Te.rebind
                                            ~attrs:(attach_attrib _loc a)
                                            ~loc:_loc (id_loc li _loc_li)
                                            (id_loc cn _loc_cn))
                         post_item_attributes)));
             Earley.apply_position
               (fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos
                           in
                        fun ((name,args,res,a) as _default_0)  ->
                          Te.decl ~attrs:(attach_attrib _loc a) ~loc:_loc
                            ~args ?res name) (constr_decl with_bar)])
      
    let _ =
      set_grammar constr_decl_list
        (Earley.alternatives
           [Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence (type_constr_decl false)
             (Earley.apply (fun cds  -> fun cd  -> cd :: cds)
                (Earley.apply List.rev
                   (Earley.fixpoint []
                      (Earley.apply (fun x  -> fun y  -> x :: y)
                         (type_constr_decl true)))));
           Earley.fsequence (Earley.char '$' '$')
             (Earley.fsequence (Earley.no_blank_test ())
                (Earley.fsequence (expression_lvl (NoMatch, App))
                   (Earley.fsequence (Earley.no_blank_test ())
                      (Earley.fsequence (Earley.char '$' '$')
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun cds  ->
                                       fun _  ->
                                         fun _  ->
                                           fun e  ->
                                             fun _  ->
                                               fun dol  ->
                                                 (list_antiquotation _loc e)
                                                   @ cds) constr_decl_list)))))])
      
    let constr_extn_list = Earley.declare_grammar "constr_extn_list" 
    let _ =
      Earley.set_grammar constr_extn_list
        (Earley.alternatives
           [Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence (type_constr_extn false)
             (Earley.apply (fun cds  -> fun cd  -> cd :: cds)
                (Earley.apply List.rev
                   (Earley.fixpoint []
                      (Earley.apply (fun x  -> fun y  -> x :: y)
                         (type_constr_extn true)))));
           Earley.fsequence (Earley.char '$' '$')
             (Earley.fsequence (Earley.no_blank_test ())
                (Earley.fsequence (expression_lvl (NoMatch, App))
                   (Earley.fsequence (Earley.no_blank_test ())
                      (Earley.fsequence (Earley.char '$' '$')
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun cds  ->
                                       fun _  ->
                                         fun _  ->
                                           fun e  ->
                                             fun _  ->
                                               fun dol  ->
                                                 (list_antiquotation _loc e)
                                                   @ cds) constr_extn_list)))))])
      
    let field_decl_semi = Earley.declare_grammar "field_decl_semi" 
    let _ =
      Earley.set_grammar field_decl_semi
        (Earley.fsequence mutable_flag
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 field_name)
              (Earley.fsequence (Earley.string ":" ":")
                 (Earley.fsequence poly_typexpr
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _default_0  ->
                                  fun pte  ->
                                    fun _  ->
                                      fun fn  ->
                                        let (_loc_fn,fn) = fn  in
                                        fun m  ->
                                          label_declaration
                                            ~attributes:(attach_attrib _loc
                                                           []) _loc
                                            (id_loc fn _loc_fn) m pte)
                       semi_col)))))
      
    let field_decl = Earley.declare_grammar "field_decl" 
    let _ =
      Earley.set_grammar field_decl
        (Earley.fsequence mutable_flag
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 field_name)
              (Earley.fsequence (Earley.string ":" ":")
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun pte  ->
                               fun _  ->
                                 fun fn  ->
                                   let (_loc_fn,fn) = fn  in
                                   fun m  ->
                                     label_declaration
                                       ~attributes:(attach_attrib _loc [])
                                       _loc (id_loc fn _loc_fn) m pte)
                    poly_typexpr))))
      
    let field_decl_aux = Earley.declare_grammar "field_decl_aux" 
    let _ =
      Earley.set_grammar field_decl_aux
        (Earley.alternatives
           [Earley.fsequence (Earley.char '$' '$')
              (Earley.fsequence (Earley.no_blank_test ())
                 (Earley.fsequence (expression_lvl (NoMatch, App))
                    (Earley.fsequence (Earley.no_blank_test ())
                       (Earley.fsequence (Earley.char '$' '$')
                          (Earley.fsequence
                             (Earley.option None
                                (Earley.apply (fun x  -> Some x)
                                   (Earley.char ';' ';')))
                             (Earley.apply_position
                                (fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos
                                            in
                                         fun ls  ->
                                           fun _default_0  ->
                                             fun _  ->
                                               fun _  ->
                                                 fun e  ->
                                                   fun _  ->
                                                     fun dol  ->
                                                       list_antiquotation
                                                         _loc e)
                                field_decl_list))))));
           Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence field_decl_aux
             (Earley.apply (fun fd  -> fun fs  -> fd :: fs) field_decl_semi)])
      
    let _ =
      set_grammar field_decl_list
        (Earley.alternatives
           [Earley.fsequence field_decl_aux
              (Earley.apply (fun fd  -> fun fs  -> List.rev (fd :: fs))
                 field_decl);
           Earley.apply (fun fs  -> List.rev fs) field_decl_aux])
      
    let type_representation = Earley.declare_grammar "type_representation" 
    let _ =
      Earley.set_grammar type_representation
        (Earley.alternatives
           [Earley.apply (fun _  -> Ptype_open) (Earley.string ".." "..");
           Earley.fsequence (Earley.string "{" "{")
             (Earley.fsequence field_decl_list
                (Earley.apply
                   (fun _  -> fun fds  -> fun _  -> Ptype_record fds)
                   (Earley.string "}" "}")));
           Earley.apply
             (fun cds  -> if cds = [] then give_up (); Ptype_variant cds)
             constr_decl_list])
      
    let type_information = Earley.declare_grammar "type_information" 
    let _ =
      Earley.set_grammar type_information
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x) type_equation))
           (Earley.fsequence
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.fsequence (Earley.char '=' '=')
                       (Earley.fsequence private_flag
                          (Earley.apply
                             (fun tr  -> fun pri  -> fun _  -> (pri, tr))
                             type_representation)))))
              (Earley.apply
                 (fun cstrs  ->
                    fun ptr  ->
                      fun te  ->
                        let (pri,tkind) =
                          match ptr with
                          | None  -> (Public, Ptype_abstract)
                          | Some c -> c  in
                        (pri, te, tkind, cstrs))
                 (Earley.apply List.rev
                    (Earley.fixpoint []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          type_constraint))))))
      
    let typedef_gen att constr filter =
      Earley.fsequence type_params
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              constr)
           (Earley.fsequence type_information
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun a  ->
                            fun ti  ->
                              fun tcn  ->
                                let (_loc_tcn,tcn) = tcn  in
                                fun tps  ->
                                  fun prev_loc  ->
                                    let _loc =
                                      match (prev_loc : Location.t option)
                                      with
                                      | None  -> _loc
                                      | Some l -> merge2 l _loc  in
                                    let (pri,te,tkind,cstrs) = ti  in
                                    let (pri,te) =
                                      match te with
                                      | None  -> (pri, None)
                                      | Some (Private ,te) ->
                                          (if pri = Private then give_up ();
                                           (Private, (Some te)))
                                      | Some (_,te) -> (pri, (Some te))  in
                                    ((id_loc tcn _loc_tcn),
                                      (type_declaration
                                         ~attributes:(if att
                                                      then
                                                        attach_attrib _loc a
                                                      else []) _loc
                                         (id_loc (filter tcn) _loc_tcn) tps
                                         cstrs tkind pri te)))
                 (Earley.alternatives
                    ((if not att
                      then [Earley.apply (fun _  -> []) (Earley.empty ())]
                      else []) @
                       ((if att then [post_item_attributes] else []) @ []))))))
      
    let type_extension = Earley.declare_grammar "type_extension" 
    let _ =
      Earley.set_grammar type_extension
        (Earley.fsequence type_kw
           (Earley.fsequence type_params
              (Earley.fsequence
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    typeconstr)
                 (Earley.fsequence (Earley.string "+=" "+=")
                    (Earley.fsequence private_flag
                       (Earley.fsequence constr_extn_list
                          (Earley.apply
                             (fun attrs  ->
                                fun cds  ->
                                  fun priv  ->
                                    fun _  ->
                                      fun tcn  ->
                                        let (_loc_tcn,tcn) = tcn  in
                                        fun params  ->
                                          fun _default_0  ->
                                            let tcn = id_loc tcn _loc_tcn  in
                                            let params = params_map params
                                               in
                                            Te.mk ~attrs ~params ~priv tcn
                                              cds) post_item_attributes)))))))
      
    let typedef = Earley.declare_grammar "typedef" 
    let _ =
      Earley.set_grammar typedef
        (typedef_gen true typeconstr_name (fun x  -> x))
      
    let typedef_in_constraint =
      Earley.declare_grammar "typedef_in_constraint" 
    let _ =
      Earley.set_grammar typedef_in_constraint
        (typedef_gen false typeconstr Longident.last)
      
    let type_definition = Earley.declare_grammar "type_definition" 
    let _ =
      Earley.set_grammar type_definition
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              type_kw)
           (Earley.fsequence typedef
              (Earley.apply
                 (fun tds  ->
                    fun td  ->
                      fun l  ->
                        let (_loc_l,l) = l  in (snd (td (Some _loc_l))) ::
                          tds)
                 (Earley.apply List.rev
                    (Earley.fixpoint []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          (Earley.fsequence
                             (Earley.apply_position
                                (fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         fun x  ->
                                           ((locate str pos str' pos'), x))
                                and_kw)
                             (Earley.apply
                                (fun td  ->
                                   fun l  ->
                                     let (_loc_l,l) = l  in
                                     snd (td (Some _loc_l))) typedef))))))))
      
    let exception_definition = Earley.declare_grammar "exception_definition" 
    let _ =
      Earley.set_grammar exception_definition
        (Earley.alternatives
           [Earley.fsequence exception_kw
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun ((name,args,res,a) as _default_0)  ->
                            fun _default_1  ->
                              let cd =
                                Te.decl ~attrs:(attach_attrib _loc a)
                                  ~loc:_loc ~args ?res name
                                 in
                              (Str.exception_ ~loc:_loc cd).pstr_desc)
                 (constr_decl false));
           Earley.fsequence exception_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   constr_name)
                (Earley.fsequence (Earley.char '=' '=')
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun c  ->
                                 let (_loc_c,c) = c  in
                                 fun _  ->
                                   fun cn  ->
                                     let (_loc_cn,cn) = cn  in
                                     fun _default_0  ->
                                       (let name = id_loc cn _loc_cn  in
                                        let ex = id_loc c _loc_c  in
                                        Str.exception_ ~loc:_loc
                                          (Te.rebind ~loc:_loc name ex)).pstr_desc)
                      (Earley.apply_position
                         (fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  ->
                                  fun x  -> ((locate str pos str' pos'), x))
                         constr))))])
      
    let class_field_spec = declare_grammar "class_field_spec" 
    let class_body_type = declare_grammar "class_body_type" 
    let virt_mut = Earley.declare_grammar "virt_mut" 
    let _ =
      Earley.set_grammar virt_mut
        (Earley.alternatives
           [Earley.fsequence mutable_kw
              (Earley.apply
                 (fun _default_0  -> fun _default_1  -> (Virtual, Mutable))
                 virtual_kw);
           Earley.fsequence virtual_flag
             (Earley.apply (fun m  -> fun v  -> (v, m)) mutable_flag)])
      
    let virt_priv = Earley.declare_grammar "virt_priv" 
    let _ =
      Earley.set_grammar virt_priv
        (Earley.alternatives
           [Earley.fsequence private_kw
              (Earley.apply
                 (fun _default_0  -> fun _default_1  -> (Virtual, Private))
                 virtual_kw);
           Earley.fsequence virtual_flag
             (Earley.apply (fun p  -> fun v  -> (v, p)) private_flag)])
      
    let _ =
      set_grammar class_field_spec
        (Earley.alternatives
           [Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun ((s,l) as _default_0)  ->
                         pctf_loc _loc (Pctf_extension (s, l)))
              floating_extension;
           Earley.fsequence inherit_kw
             (Earley.apply_position
                (fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos
                            in
                         fun cbt  ->
                           fun _default_0  ->
                             pctf_loc _loc (Pctf_inherit cbt))
                class_body_type);
           Earley.fsequence val_kw
             (Earley.fsequence virt_mut
                (Earley.fsequence inst_var_name
                   (Earley.fsequence (Earley.string ":" ":")
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun te  ->
                                    fun _  ->
                                      fun ivn  ->
                                        fun ((vir,mut) as _default_0)  ->
                                          fun _default_1  ->
                                            pctf_loc _loc
                                              (Pctf_val (ivn, mut, vir, te)))
                         typexpr))));
           Earley.fsequence method_kw
             (Earley.fsequence virt_priv
                (Earley.fsequence method_name
                   (Earley.fsequence (Earley.string ":" ":")
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun te  ->
                                    fun _  ->
                                      fun mn  ->
                                        fun ((v,pri) as _default_0)  ->
                                          fun _default_1  ->
                                            Ctf.method_ ~loc:_loc mn pri v te)
                         poly_typexpr))));
           Earley.fsequence constraint_kw
             (Earley.fsequence typexpr
                (Earley.fsequence (Earley.char '=' '=')
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun te'  ->
                                 fun _  ->
                                   fun te  ->
                                     fun _default_0  ->
                                       pctf_loc _loc
                                         (Pctf_constraint (te, te'))) typexpr)));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ((s,l) as _default_0)  ->
                        pctf_loc _loc (Pctf_attribute (s, l)))
             floating_attribute])
      
    let _ =
      set_grammar class_body_type
        (Earley.alternatives
           [Earley.fsequence
              (Earley.option []
                 (Earley.fsequence (Earley.string "[" "[")
                    (Earley.fsequence typexpr
                       (Earley.fsequence
                          (Earley.apply List.rev
                             (Earley.fixpoint []
                                (Earley.apply (fun x  -> fun y  -> x :: y)
                                   (Earley.fsequence (Earley.string "," ",")
                                      (Earley.apply (fun te  -> fun _  -> te)
                                         typexpr)))))
                          (Earley.apply
                             (fun _  ->
                                fun tes  -> fun te  -> fun _  -> te :: tes)
                             (Earley.string "]" "]"))))))
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun ctp  ->
                            let (_loc_ctp,ctp) = ctp  in
                            fun tes  ->
                              let ctp = id_loc ctp _loc_ctp  in
                              pcty_loc _loc (Pcty_constr (ctp, tes)))
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    classtype_path));
           Earley.fsequence object_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   (Earley.option None
                      (Earley.apply (fun x  -> Some x)
                         (Earley.fsequence (Earley.string "(" "(")
                            (Earley.fsequence typexpr
                               (Earley.apply
                                  (fun _  -> fun te  -> fun _  -> te)
                                  (Earley.string ")" ")")))))))
                (Earley.fsequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            class_field_spec)))
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun _default_0  ->
                                 fun cfs  ->
                                   fun te  ->
                                     let (_loc_te,te) = te  in
                                     fun _default_1  ->
                                       let self =
                                         match te with
                                         | None  -> loc_typ _loc_te Ptyp_any
                                         | Some t -> t  in
                                       let sign =
                                         {
                                           pcsig_self = self;
                                           pcsig_fields = cfs
                                         }  in
                                       pcty_loc _loc (Pcty_signature sign))
                      end_kw)))])
      
    let class_type = Earley.declare_grammar "class_type" 
    let _ =
      Earley.set_grammar class_type
        (Earley.fsequence
           (Earley.apply List.rev
              (Earley.fixpoint []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x) maybe_opt_label))
                       (Earley.fsequence (Earley.string ":" ":")
                          (Earley.apply
                             (fun te  -> fun _  -> fun l  -> (l, te)) typexpr))))))
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun cbt  ->
                         fun tes  ->
                           let app acc (lab,te) =
                             match lab with
                             | None  ->
                                 pcty_loc _loc
                                   (Pcty_arrow (nolabel, te, acc))
                             | Some l ->
                                 pcty_loc _loc
                                   (Pcty_arrow
                                      (l,
                                        (match l with
                                         | Optional _ -> te
                                         | _ -> te), acc))
                              in
                           List.fold_left app cbt (List.rev tes))
              class_body_type))
      
    let type_parameters = Earley.declare_grammar "type_parameters" 
    let _ =
      Earley.set_grammar type_parameters
        (Earley.fsequence type_param
           (Earley.apply (fun l  -> fun i1  -> i1 :: l)
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.fsequence (Earley.string "," ",")
                          (Earley.apply (fun i2  -> fun _  -> i2) type_param)))))))
      
    let class_spec = Earley.declare_grammar "class_spec" 
    let _ =
      Earley.set_grammar class_spec
        (Earley.fsequence virtual_flag
           (Earley.fsequence
              (Earley.option []
                 (Earley.fsequence (Earley.string "[" "[")
                    (Earley.fsequence type_parameters
                       (Earley.apply
                          (fun _  -> fun params  -> fun _  -> params)
                          (Earley.string "]" "]")))))
              (Earley.fsequence
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    class_name)
                 (Earley.fsequence (Earley.string ":" ":")
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun ct  ->
                                  fun _  ->
                                    fun cn  ->
                                      let (_loc_cn,cn) = cn  in
                                      fun params  ->
                                        fun v  ->
                                          class_type_declaration
                                            ~attributes:(attach_attrib _loc
                                                           []) _loc
                                            (id_loc cn _loc_cn) params v ct)
                       class_type)))))
      
    let class_specification = Earley.declare_grammar "class_specification" 
    let _ =
      Earley.set_grammar class_specification
        (Earley.fsequence class_kw
           (Earley.fsequence class_spec
              (Earley.apply
                 (fun css  -> fun cs  -> fun _default_0  -> cs :: css)
                 (Earley.apply List.rev
                    (Earley.fixpoint []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          (Earley.fsequence and_kw
                             (Earley.apply
                                (fun _default_0  -> fun _  -> _default_0)
                                class_spec))))))))
      
    let classtype_def = Earley.declare_grammar "classtype_def" 
    let _ =
      Earley.set_grammar classtype_def
        (Earley.fsequence virtual_flag
           (Earley.fsequence
              (Earley.option []
                 (Earley.fsequence (Earley.string "[" "[")
                    (Earley.fsequence type_parameters
                       (Earley.apply (fun _  -> fun tp  -> fun _  -> tp)
                          (Earley.string "]" "]")))))
              (Earley.fsequence
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    class_name)
                 (Earley.fsequence (Earley.char '=' '=')
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun cbt  ->
                                  fun _  ->
                                    fun cn  ->
                                      let (_loc_cn,cn) = cn  in
                                      fun params  ->
                                        fun v  ->
                                          fun _loc  ->
                                            class_type_declaration
                                              ~attributes:(attach_attrib _loc
                                                             []) _loc
                                              (id_loc cn _loc_cn) params v
                                              cbt) class_body_type)))))
      
    let classtype_definition = Earley.declare_grammar "classtype_definition" 
    let _ =
      Earley.set_grammar classtype_definition
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              class_kw)
           (Earley.fsequence type_kw
              (Earley.fsequence
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    classtype_def)
                 (Earley.apply
                    (fun cds  ->
                       fun cd  ->
                         let (_loc_cd,cd) = cd  in
                         fun _default_0  ->
                           fun k  ->
                             let (_loc_k,k) = k  in
                             (cd (merge2 _loc_k _loc_cd)) :: cds)
                    (Earley.apply List.rev
                       (Earley.fixpoint []
                          (Earley.apply (fun x  -> fun y  -> x :: y)
                             (Earley.fsequence and_kw
                                (Earley.apply_position
                                   (fun __loc__start__buf  ->
                                      fun __loc__start__pos  ->
                                        fun __loc__end__buf  ->
                                          fun __loc__end__pos  ->
                                            let _loc =
                                              locate __loc__start__buf
                                                __loc__start__pos
                                                __loc__end__buf
                                                __loc__end__pos
                                               in
                                            fun cd  -> fun _  -> cd _loc)
                                   classtype_def)))))))))
      
    let constant = Earley.declare_grammar "constant" 
    let _ =
      Earley.set_grammar constant
        (Earley.alternatives
           [Earley.apply
              (fun ((i,suffix) as _default_0)  -> Const.integer ?suffix i)
              int_litteral;
           Earley.apply
             (fun ((f,suffix) as _default_0)  -> Const.float ?suffix f)
             float_litteral;
           Earley.apply (fun c  -> Const.char c) char_litteral;
           Earley.apply
             (fun ((s,delim) as _default_0)  ->
                Const.string ?quotation_delimiter:delim s) string_litteral;
           Earley.apply (fun s  -> const_string s) regexp_litteral;
           Earley.apply (fun s  -> const_string s) new_regexp_litteral])
      
    let neg_constant = Earley.declare_grammar "neg_constant" 
    let _ =
      Earley.set_grammar neg_constant
        (Earley.alternatives
           [Earley.fsequence (Earley.char '-' '-')
              (Earley.apply
                 (fun ((i,suffix) as _default_0)  ->
                    fun _  -> Const.integer ?suffix ("-" ^ i)) int_litteral);
           Earley.fsequence (Earley.char '-' '-')
             (Earley.fsequence (Earley.no_blank_test ())
                (Earley.fsequence
                   (Earley.option None
                      (Earley.apply (fun x  -> Some x) (Earley.char '.' '.')))
                   (Earley.apply
                      (fun ((f,suffix) as _default_0)  ->
                         fun _default_1  ->
                           fun _  -> fun _  -> Const.float ?suffix ("-" ^ f))
                      float_litteral)))])
      
    let (extra_patterns_grammar,extra_patterns_grammar__set__grammar) =
      Earley.grammar_family "extra_patterns_grammar" 
    let _ =
      extra_patterns_grammar__set__grammar
        (fun lvl  -> alternatives (List.map (fun g  -> g lvl) extra_patterns))
      
    let _ =
      set_pattern_lvl
        ([(((fun (as_ok,lvl)  -> lvl <= AtomPat)),
            (Earley.fsequence (Earley.char '$' '$')
               (Earley.fsequence (Earley.no_blank_test ())
                  (Earley.fsequence
                     (Earley.option "pat"
                        (Earley.fsequence
                           (EarleyStr.regexp ~name:"[a-z]+" "[a-z]+"
                              (fun groupe  -> groupe 0))
                           (Earley.fsequence (Earley.no_blank_test ())
                              (Earley.apply
                                 (fun _  ->
                                    fun _  -> fun _default_0  -> _default_0)
                                 (Earley.char ':' ':')))))
                     (Earley.fsequence expression
                        (Earley.fsequence (Earley.no_blank_test ())
                           (Earley.apply_position
                              (fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos
                                          in
                                       fun _  ->
                                         fun _  ->
                                           fun e  ->
                                             fun aq  ->
                                               fun _  ->
                                                 fun _  ->
                                                   let open Quote in
                                                     let e_loc =
                                                       exp_ident _loc "_loc"
                                                        in
                                                     let locate _loc e =
                                                       quote_record e_loc
                                                         _loc
                                                         [((parsetree
                                                              "ppat_desc"),
                                                            e);
                                                         ((parsetree
                                                             "ppat_loc"),
                                                           (quote_location_t
                                                              e_loc _loc _loc));
                                                         ((parsetree
                                                             "ppat_attributes"),
                                                           (quote_attributes
                                                              e_loc _loc []))]
                                                        in
                                                     let generic_antiquote e
                                                       =
                                                       function
                                                       | Quote_ppat  -> e
                                                       | _ ->
                                                           failwith
                                                             ("invalid antiquotation type ppat expected at "
                                                                ^
                                                                (string_location
                                                                   _loc))
                                                        in
                                                     let f =
                                                       match aq with
                                                       | "pat" ->
                                                           generic_antiquote
                                                             e
                                                       | "bool" ->
                                                           let e =
                                                             quote_const
                                                               e_loc _loc
                                                               (parsetree
                                                                  "Ppat_constant")
                                                               [quote_apply
                                                                  e_loc _loc
                                                                  (pa_ast
                                                                    "const_bool")
                                                                  [e]]
                                                              in
                                                           generic_antiquote
                                                             (locate _loc e)
                                                       | "int" ->
                                                           let e =
                                                             quote_const
                                                               e_loc _loc
                                                               (parsetree
                                                                  "Ppat_constant")
                                                               [quote_apply
                                                                  e_loc _loc
                                                                  (pa_ast
                                                                    "const_int")
                                                                  [e]]
                                                              in
                                                           generic_antiquote
                                                             (locate _loc e)
                                                       | "string" ->
                                                           let e =
                                                             quote_const
                                                               e_loc _loc
                                                               (parsetree
                                                                  "Ppat_constant")
                                                               [quote_apply
                                                                  e_loc _loc
                                                                  (pa_ast
                                                                    "const_string")
                                                                  [e]]
                                                              in
                                                           generic_antiquote
                                                             (locate _loc e)
                                                       | "list" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "pat_list")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                quote_location_t
                                                                  e_loc _loc
                                                                  _loc;
                                                                e])
                                                       | "tuple" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "pat_tuple")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "array" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "pat_array")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | _ -> give_up ()  in
                                                     Quote.ppat_antiquotation
                                                       _loc f)
                              (Earley.char '$' '$'))))))));
         (((fun _  -> true)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun vn  ->
                         let (_loc_vn,vn) = vn  in
                         Pat.var ~loc:_loc (id_loc vn _loc_vn))
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 value_name)));
         (((fun _  -> true)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun _default_0  -> Pat.any ~loc:_loc ()) joker_kw));
         (((fun _  -> true)),
           (Earley.fsequence char_litteral
              (Earley.fsequence (Earley.string ".." "..")
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun c2  ->
                               fun _  ->
                                 fun c1  ->
                                   Pat.interval ~loc:_loc (Const.char c1)
                                     (Const.char c2)) char_litteral))));
         (((fun (as_ok,lvl)  -> lvl <= AtomPat)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun c  -> Pat.constant ~loc:_loc c)
              (Earley.alternatives [neg_constant; constant])));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence pattern
                 (Earley.fsequence
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x)
                          (Earley.fsequence (Earley.char ':' ':')
                             (Earley.apply
                                (fun _default_0  -> fun _  -> _default_0)
                                typexpr))))
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun ty  ->
                                    fun p  ->
                                      fun _  ->
                                        let p =
                                          match ty with
                                          | None  -> loc_pat _loc p.ppat_desc
                                          | Some ty ->
                                              Pat.constraint_ ~loc:_loc p ty
                                           in
                                        p) (Earley.char ')' ')'))))));
         (((fun (as_ok,lvl)  -> lvl <= ConstrPat)),
           (Earley.fsequence lazy_kw
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun p  -> fun _default_0  -> Pat.lazy_ ~loc:_loc p)
                 (pattern_lvl (false, ConstrPat)))));
         (((fun (as_ok,lvl)  -> lvl <= ConstrPat)),
           (Earley.fsequence exception_kw
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun p  ->
                            fun _default_0  -> Pat.exception_ ~loc:_loc p)
                 (pattern_lvl (false, ConstrPat)))));
         (((fun (as_ok,lvl)  -> lvl <= ConstrPat)),
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x)) constr)
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun p  ->
                            fun c  ->
                              let (_loc_c,c) = c  in
                              Pat.construct ~loc:_loc (id_loc c _loc_c)
                                (Some p)) (pattern_lvl (false, ConstrPat)))));
         (((fun _  -> true)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun c  ->
                         let (_loc_c,c) = c  in
                         Pat.construct ~loc:_loc (id_loc c _loc_c) None)
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x)) constr)));
         (((fun _  -> true)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun b  ->
                         Pat.construct ~loc:_loc (id_loc (Lident b) _loc)
                           None) bool_lit));
         (((fun (as_ok,lvl)  -> lvl <= ConstrPat)),
           (Earley.fsequence tag_name
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun p  ->
                            fun c  -> Pat.variant ~loc:_loc c (Some p))
                 (pattern_lvl (false, ConstrPat)))));
         (((fun _  -> true)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun c  -> Pat.variant ~loc:_loc c None) tag_name));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '#' '#')
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun t  ->
                            let (_loc_t,t) = t  in
                            fun s  -> Pat.type_ ~loc:_loc (id_loc t _loc_t))
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    typeconstr))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '{' '{')
              (Earley.fsequence
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x)) field)
                 (Earley.fsequence
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x)
                          (Earley.fsequence (Earley.char '=' '=')
                             (Earley.apply (fun p  -> fun _  -> p) pattern))))
                    (Earley.fsequence
                       (Earley.apply List.rev
                          (Earley.fixpoint []
                             (Earley.apply (fun x  -> fun y  -> x :: y)
                                (Earley.fsequence semi_col
                                   (Earley.fsequence
                                      (Earley.apply_position
                                         (fun str  ->
                                            fun pos  ->
                                              fun str'  ->
                                                fun pos'  ->
                                                  fun x  ->
                                                    ((locate str pos str'
                                                        pos'), x)) field)
                                      (Earley.apply
                                         (fun p  ->
                                            fun f  ->
                                              let (_loc_f,f) = f  in
                                              fun _default_0  ->
                                                ((id_loc f _loc_f), p))
                                         (Earley.option None
                                            (Earley.apply (fun x  -> Some x)
                                               (Earley.fsequence
                                                  (Earley.char '=' '=')
                                                  (Earley.apply
                                                     (fun p  -> fun _  -> p)
                                                     pattern))))))))))
                       (Earley.fsequence
                          (Earley.option None
                             (Earley.apply (fun x  -> Some x)
                                (Earley.fsequence semi_col
                                   (Earley.apply
                                      (fun _default_0  ->
                                         fun _default_1  -> ()) joker_kw))))
                          (Earley.fsequence
                             (Earley.option None
                                (Earley.apply (fun x  -> Some x) semi_col))
                             (Earley.apply_position
                                (fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos
                                            in
                                         fun _  ->
                                           fun _default_0  ->
                                             fun clsd  ->
                                               fun fps  ->
                                                 fun p  ->
                                                   fun f  ->
                                                     let (_loc_f,f) = f  in
                                                     fun s  ->
                                                       let all =
                                                         ((id_loc f _loc_f),
                                                           p)
                                                         :: fps  in
                                                       let f (lab,pat) =
                                                         match pat with
                                                         | Some p -> (lab, p)
                                                         | None  ->
                                                             let slab =
                                                               match lab.txt
                                                               with
                                                               | Lident s ->
                                                                   id_loc s
                                                                    lab.loc
                                                               | _ ->
                                                                   give_up ()
                                                                in
                                                             (lab,
                                                               (loc_pat
                                                                  lab.loc
                                                                  (Ppat_var
                                                                    slab)))
                                                          in
                                                       let all =
                                                         List.map f all  in
                                                       let cl =
                                                         match clsd with
                                                         | None  -> Closed
                                                         | Some _ -> Open  in
                                                       Pat.record ~loc:_loc
                                                         all cl)
                                (Earley.char '}' '}')))))))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '[' '[')
              (Earley.fsequence (list1 pattern semi_col)
                 (Earley.fsequence
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x) semi_col))
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun c  ->
                                  let (_loc_c,c) = c  in
                                  fun _default_0  ->
                                    fun ps  ->
                                      fun _  -> pat_list _loc _loc_c ps)
                       (Earley.apply_position
                          (fun str  ->
                             fun pos  ->
                               fun str'  ->
                                 fun pos'  ->
                                   fun x  -> ((locate str pos str' pos'), x))
                          (Earley.char ']' ']')))))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '[' '[')
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun _  ->
                            fun _  ->
                              Pat.construct ~loc:_loc
                                (id_loc (Lident "[]") _loc) None)
                 (Earley.char ']' ']'))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.string "[|" "[|")
              (Earley.fsequence (list0 pattern semi_col)
                 (Earley.fsequence
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x) semi_col))
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun _default_0  ->
                                    fun ps  ->
                                      fun _  -> Pat.array ~loc:_loc ps)
                       (Earley.string "|]" "|]"))))));
         (((fun _  -> true)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun _  ->
                            fun _  ->
                              Pat.construct ~loc:_loc
                                (id_loc (Lident "()") _loc) None)
                 (Earley.char ')' ')'))));
         (((fun _  -> true)),
           (Earley.fsequence begin_kw
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun _default_0  ->
                            fun _default_1  ->
                              Pat.construct ~loc:_loc
                                (id_loc (Lident "()") _loc) None) end_kw)));
         (((fun (as_ok,lvl)  -> lvl <= AtomPat)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence module_kw
                 (Earley.fsequence module_name
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x)
                             (Earley.fsequence (Earley.string ":" ":")
                                (Earley.apply (fun pt  -> fun _  -> pt)
                                   package_type))))
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _  ->
                                     fun pt  ->
                                       fun mn  ->
                                         fun _default_0  ->
                                           fun _  ->
                                             let unpack = Ppat_unpack mn  in
                                             let pat =
                                               match pt with
                                               | None  -> unpack
                                               | Some pt ->
                                                   let pt =
                                                     loc_typ (ghost _loc)
                                                       pt.ptyp_desc
                                                      in
                                                   Ppat_constraint
                                                     ((loc_pat _loc unpack),
                                                       pt)
                                                in
                                             loc_pat _loc pat)
                          (Earley.char ')' ')')))))));
         (((fun (as_ok,lvl)  -> lvl <= AltPat)),
           (Earley.fsequence (pattern_lvl (true, AltPat))
              (Earley.fsequence (Earley.char '|' '|')
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun p'  ->
                               fun _  -> fun p  -> Pat.or_ ~loc:_loc p p')
                    (pattern_lvl (false, (next_pat_prio AltPat)))))));
         (((fun (as_ok,lvl)  -> lvl <= TupPat)),
           (Earley.fsequence
              (Earley.apply List.rev
                 (Earley.fixpoint1 []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.fsequence
                          (pattern_lvl (true, (next_pat_prio TupPat)))
                          (Earley.apply
                             (fun _  -> fun _default_0  -> _default_0)
                             (Earley.char ',' ','))))))
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun p  -> fun ps  -> Pat.tuple ~loc:_loc (ps @ [p]))
                 (pattern_lvl (false, (next_pat_prio TupPat))))));
         (((fun (as_ok,lvl)  -> lvl <= ConsPat)),
           (Earley.fsequence (pattern_lvl (true, (next_pat_prio ConsPat)))
              (Earley.fsequence
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    (Earley.string "::" "::"))
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun p'  ->
                               fun c  ->
                                 let (_loc_c,c) = c  in
                                 fun p  ->
                                   let cons = id_loc (Lident "::") _loc_c  in
                                   let args =
                                     loc_pat (ghost _loc)
                                       (Ppat_tuple [p; p'])
                                      in
                                   Pat.construct ~loc:_loc cons (Some args))
                    (pattern_lvl (false, ConsPat))))));
         (((fun (as_ok,lvl)  -> lvl <= AtomPat)),
           (Earley.fsequence (Earley.char '$' '$')
              (Earley.fsequence (Earley.no_blank_test ())
                 (Earley.apply
                    (fun c  ->
                       fun _  ->
                         fun _  ->
                           try
                             let str = Sys.getenv c  in
                             parse_string ~filename:("ENV:" ^ c) pattern
                               ocaml_blank str
                           with | Not_found  -> give_up ()) uident))))],
          (fun (as_ok,lvl)  -> (extra_patterns_grammar (as_ok, lvl)) ::
             ((if as_ok
               then
                 [Earley.fsequence (pattern_lvl (as_ok, lvl))
                    (Earley.fsequence as_kw
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun vn  ->
                                     let (_loc_vn,vn) = vn  in
                                     fun _default_0  ->
                                       fun p  ->
                                         Pat.alias ~loc:_loc p
                                           (id_loc vn _loc_vn))
                          (Earley.apply_position
                             (fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      fun x  ->
                                        ((locate str pos str' pos'), x))
                             value_name)))]
               else []) @ [])))
      
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
      let name = if !fast then "unsafe_" ^ name else name  in
      loc_expr loc (Pexp_ident (id_loc (Ldot ((Lident str), name)) loc)) 
    let bigarray_function loc str name =
      let name = if !fast then "unsafe_" ^ name else name  in
      let lid = Ldot ((Ldot ((Lident "Bigarray"), str)), name)  in
      loc_expr loc (Pexp_ident (id_loc lid loc)) 
    let untuplify exp =
      match exp.pexp_desc with | Pexp_tuple es -> es | _ -> [exp] 
    let bigarray_get _loc arr arg =
      let get = if !fast then "unsafe_get" else "get"  in
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
                                    ((Longident.Lident "Bigarray"), "Array1")),
                                  get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }, [(Asttypes.Nolabel, arr); (Asttypes.Nolabel, c1)]));
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
                                    ((Longident.Lident "Bigarray"), "Array2")),
                                  get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel, arr);
                   (Asttypes.Nolabel, c1);
                   (Asttypes.Nolabel, c2)]));
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
                                    ((Longident.Lident "Bigarray"), "Array3")),
                                  get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel, arr);
                   (Asttypes.Nolabel, c1);
                   (Asttypes.Nolabel, c2);
                   (Asttypes.Nolabel, c3)]));
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
                                    ((Longident.Lident "Bigarray"),
                                      "Genarray")), get));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel, arr);
                   (Asttypes.Nolabel, (Pa_ast.exp_array _loc coords))]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
      
    let bigarray_set _loc arr arg newval =
      let set = if !fast then "unsafe_set" else "set"  in
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
                                    ((Longident.Lident "Bigarray"), "Array1")),
                                  set));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel, arr);
                   (Asttypes.Nolabel, c1);
                   (Asttypes.Nolabel, newval)]));
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
                                    ((Longident.Lident "Bigarray"), "Array2")),
                                  set));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel, arr);
                   (Asttypes.Nolabel, c1);
                   (Asttypes.Nolabel, c2);
                   (Asttypes.Nolabel, newval)]));
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
                                    ((Longident.Lident "Bigarray"), "Array3")),
                                  set));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel, arr);
                   (Asttypes.Nolabel, c1);
                   (Asttypes.Nolabel, c2);
                   (Asttypes.Nolabel, c3);
                   (Asttypes.Nolabel, newval)]));
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
                                    ((Longident.Lident "Bigarray"),
                                      "Genarray")), set));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel, arr);
                   (Asttypes.Nolabel, (Pa_ast.exp_array _loc coords));
                   (Asttypes.Nolabel, newval)]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
      
    let constructor = Earley.declare_grammar "constructor" 
    let _ =
      Earley.set_grammar constructor
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence module_path
                    (Earley.apply (fun _  -> fun m  -> m)
                       (Earley.string "." ".")))))
           (Earley.apply
              (fun id  ->
                 fun m  ->
                   match m with | None  -> Lident id | Some m -> Ldot (m, id))
              (Earley.alternatives [bool_lit; uident])))
      
    let argument = Earley.declare_grammar "argument" 
    let _ =
      Earley.set_grammar argument
        (Earley.alternatives
           [Earley.apply (fun e  -> (nolabel, e))
              (expression_lvl (NoMatch, (next_exp App)));
           Earley.fsequence (Earley.char '~' '~')
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x)) lident)
                (Earley.apply
                   (fun _default_0  ->
                      fun id  ->
                        let (_loc_id,id) = id  in
                        fun _  ->
                          ((labelled id),
                            (loc_expr _loc_id
                               (Pexp_ident (id_loc (Lident id) _loc_id)))))
                   no_colon));
           Earley.fsequence ty_label
             (Earley.apply (fun e  -> fun id  -> (id, e))
                (expression_lvl (NoMatch, (next_exp App))));
           Earley.fsequence (Earley.char '?' '?')
             (Earley.apply
                (fun id  ->
                   let (_loc_id,id) = id  in
                   fun _  ->
                     ((optional id),
                       (Exp.ident ~loc:_loc_id (id_loc (Lident id) _loc_id))))
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x)) lident));
           Earley.fsequence ty_opt_label
             (Earley.apply (fun e  -> fun id  -> (id, e))
                (expression_lvl (NoMatch, (next_exp App))))])
      
    let _ =
      set_parameter
        (fun allow_new_type  ->
           Earley.alternatives
             ((if allow_new_type
               then
                 [Earley.fsequence (Earley.char '(' '(')
                    (Earley.fsequence type_kw
                       (Earley.fsequence
                          (Earley.apply_position
                             (fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      fun x  ->
                                        ((locate str pos str' pos'), x))
                             typeconstr_name)
                          (Earley.apply
                             (fun _  ->
                                fun name  ->
                                  let (_loc_name,name) = name  in
                                  fun _default_0  ->
                                    fun _  ->
                                      let name = id_loc name _loc_name  in
                                      `Type name) (Earley.char ')' ')'))))]
               else []) @
                [Earley.apply (fun pat  -> `Arg (nolabel, None, pat))
                   (pattern_lvl (false, AtomPat));
                Earley.fsequence (Earley.char '~' '~')
                  (Earley.fsequence (Earley.char '(' '(')
                     (Earley.fsequence
                        (Earley.apply_position
                           (fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    fun x  -> ((locate str pos str' pos'), x))
                           lident)
                        (Earley.fsequence
                           (Earley.option None
                              (Earley.apply (fun x  -> Some x)
                                 (Earley.fsequence (Earley.string ":" ":")
                                    (Earley.apply (fun t  -> fun _  -> t)
                                       typexpr))))
                           (Earley.apply_position
                              (fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos
                                          in
                                       fun _  ->
                                         fun t  ->
                                           fun id  ->
                                             let (_loc_id,id) = id  in
                                             fun _  ->
                                               fun _  ->
                                                 let pat =
                                                   loc_pat _loc_id
                                                     (Ppat_var
                                                        (id_loc id _loc_id))
                                                    in
                                                 let pat =
                                                   match t with
                                                   | None  -> pat
                                                   | Some t ->
                                                       loc_pat _loc
                                                         (Ppat_constraint
                                                            (pat, t))
                                                    in
                                                 `Arg
                                                   ((labelled id), None, pat))
                              (Earley.string ")" ")")))));
                Earley.fsequence ty_label
                  (Earley.apply (fun pat  -> fun id  -> `Arg (id, None, pat))
                     pattern);
                Earley.fsequence (Earley.char '~' '~')
                  (Earley.fsequence
                     (Earley.apply_position
                        (fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  ->
                                 fun x  -> ((locate str pos str' pos'), x))
                        lident)
                     (Earley.apply
                        (fun _default_0  ->
                           fun id  ->
                             let (_loc_id,id) = id  in
                             fun _  ->
                               `Arg
                                 ((labelled id), None,
                                   (loc_pat _loc_id
                                      (Ppat_var (id_loc id _loc_id)))))
                        no_colon));
                Earley.fsequence (Earley.char '?' '?')
                  (Earley.fsequence (Earley.char '(' '(')
                     (Earley.fsequence
                        (Earley.apply_position
                           (fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    fun x  -> ((locate str pos str' pos'), x))
                           lident)
                        (Earley.fsequence
                           (Earley.apply_position
                              (fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       fun x  ->
                                         ((locate str pos str' pos'), x))
                              (Earley.option None
                                 (Earley.apply (fun x  -> Some x)
                                    (Earley.fsequence (Earley.char ':' ':')
                                       (Earley.apply (fun t  -> fun _  -> t)
                                          typexpr)))))
                           (Earley.fsequence
                              (Earley.option None
                                 (Earley.apply (fun x  -> Some x)
                                    (Earley.fsequence (Earley.char '=' '=')
                                       (Earley.apply (fun e  -> fun _  -> e)
                                          expression))))
                              (Earley.apply
                                 (fun _  ->
                                    fun e  ->
                                      fun t  ->
                                        let (_loc_t,t) = t  in
                                        fun id  ->
                                          let (_loc_id,id) = id  in
                                          fun _  ->
                                            fun _  ->
                                              let pat =
                                                loc_pat _loc_id
                                                  (Ppat_var
                                                     (id_loc id _loc_id))
                                                 in
                                              let pat =
                                                match t with
                                                | None  -> pat
                                                | Some t ->
                                                    loc_pat
                                                      (merge2 _loc_id _loc_t)
                                                      (Ppat_constraint
                                                         (pat, t))
                                                 in
                                              `Arg ((optional id), e, pat))
                                 (Earley.char ')' ')'))))));
                Earley.fsequence ty_opt_label
                  (Earley.fsequence (Earley.string "(" "(")
                     (Earley.fsequence
                        (Earley.apply_position
                           (fun str  ->
                              fun pos  ->
                                fun str'  ->
                                  fun pos'  ->
                                    fun x  -> ((locate str pos str' pos'), x))
                           pattern)
                        (Earley.fsequence
                           (Earley.apply_position
                              (fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       fun x  ->
                                         ((locate str pos str' pos'), x))
                              (Earley.option None
                                 (Earley.apply (fun x  -> Some x)
                                    (Earley.fsequence (Earley.char ':' ':')
                                       (Earley.apply (fun t  -> fun _  -> t)
                                          typexpr)))))
                           (Earley.fsequence
                              (Earley.option None
                                 (Earley.apply (fun x  -> Some x)
                                    (Earley.fsequence (Earley.char '=' '=')
                                       (Earley.apply (fun e  -> fun _  -> e)
                                          expression))))
                              (Earley.apply
                                 (fun _  ->
                                    fun e  ->
                                      fun t  ->
                                        let (_loc_t,t) = t  in
                                        fun pat  ->
                                          let (_loc_pat,pat) = pat  in
                                          fun _  ->
                                            fun id  ->
                                              let pat =
                                                match t with
                                                | None  -> pat
                                                | Some t ->
                                                    loc_pat
                                                      (merge2 _loc_pat _loc_t)
                                                      (Ppat_constraint
                                                         (pat, t))
                                                 in
                                              `Arg (id, e, pat))
                                 (Earley.char ')' ')'))))));
                Earley.fsequence ty_opt_label
                  (Earley.apply (fun pat  -> fun id  -> `Arg (id, None, pat))
                     pattern);
                Earley.fsequence (Earley.char '?' '?')
                  (Earley.apply
                     (fun id  ->
                        let (_loc_id,id) = id  in
                        fun _  ->
                          `Arg
                            ((optional id), None,
                              (loc_pat _loc_id (Ppat_var (id_loc id _loc_id)))))
                     (Earley.apply_position
                        (fun str  ->
                           fun pos  ->
                             fun str'  ->
                               fun pos'  ->
                                 fun x  -> ((locate str pos str' pos'), x))
                        lident))]))
      
    let apply_params ?(gh= false)  _loc params e =
      let f acc =
        function
        | (`Arg (lbl,opt,pat),_loc') ->
            loc_expr (ghost (merge2 _loc' _loc))
              (pexp_fun (lbl, opt, pat, acc))
        | (`Type name,_loc') -> Exp.newtype ~loc:(merge2 _loc' _loc) name acc
         in
      let e = List.fold_left f e (List.rev params)  in
      if gh then e else de_ghost e 
    [@@@ocaml.text
      " FIXME OCAML: should be ghost, or above should not be ghost "]
    let apply_params_cls ?(gh= false)  _loc params e =
      let ghost _loc' = if gh then merge2 _loc' _loc else _loc  in
      let f acc =
        function
        | (`Arg (lbl,opt,pat),_loc') ->
            loc_pcl (ghost _loc') (Pcl_fun (lbl, opt, pat, acc))
        | (`Type name,_) -> assert false  in
      List.fold_left f e (List.rev params) 
    [@@@ocaml.text " FIXME OCAML: shoud be ghost as above ? "]
    let right_member = Earley.declare_grammar "right_member" 
    let _ =
      Earley.set_grammar right_member
        (Earley.fsequence
           (Earley.apply List.rev
              (Earley.fixpoint1 []
                 (Earley.apply (fun x  -> fun y  -> x :: y)
                    (Earley.apply
                       (fun lb  -> let (_loc_lb,lb) = lb  in (lb, _loc_lb))
                       (Earley.apply_position
                          (fun str  ->
                             fun pos  ->
                               fun str'  ->
                                 fun pos'  ->
                                   fun x  -> ((locate str pos str' pos'), x))
                          (parameter true))))))
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x)
                       (Earley.fsequence (Earley.char ':' ':')
                          (Earley.apply (fun t  -> fun _  -> t) typexpr)))))
              (Earley.fsequence (Earley.char '=' '=')
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun e  ->
                               let (_loc_e,e) = e  in
                               fun _  ->
                                 fun ty  ->
                                   let (_loc_ty,ty) = ty  in
                                   fun l  ->
                                     let e =
                                       match ty with
                                       | None  -> e
                                       | Some ty ->
                                           loc_expr
                                             (ghost (merge2 _loc_ty _loc))
                                             (pexp_constraint (e, ty))
                                        in
                                     apply_params ~gh:true _loc_e l e)
                    (Earley.apply_position
                       (fun str  ->
                          fun pos  ->
                            fun str'  ->
                              fun pos'  ->
                                fun x  -> ((locate str pos str' pos'), x))
                       expression)))))
      
    let eright_member = Earley.declare_grammar "eright_member" 
    let _ =
      Earley.set_grammar eright_member
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x)
                 (Earley.fsequence (Earley.char ':' ':')
                    (Earley.apply (fun t  -> fun _  -> t) typexpr))))
           (Earley.fsequence (Earley.char '=' '=')
              (Earley.apply (fun e  -> fun _  -> fun ty  -> (ty, e))
                 expression)))
      
    let _ =
      set_grammar let_binding
        (Earley.alternatives
           [Earley.fsequence (Earley.char '$' '$')
              (Earley.fsequence (Earley.no_blank_test ())
                 (Earley.fsequence
                    (Earley.option "bindings"
                       (Earley.fsequence
                          (Earley.string "bindings" "bindings")
                          (Earley.apply (fun _  -> fun c  -> c)
                             (Earley.string ":" ":"))))
                    (Earley.fsequence (expression_lvl (NoMatch, App))
                       (Earley.fsequence (Earley.no_blank_test ())
                          (Earley.fsequence (Earley.char '$' '$')
                             (Earley.apply_position
                                (fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos
                                            in
                                         fun l  ->
                                           fun _  ->
                                             fun _  ->
                                               fun e  ->
                                                 fun aq  ->
                                                   fun _  ->
                                                     fun dol  ->
                                                       let open Quote in
                                                         let generic_antiquote
                                                           e =
                                                           function
                                                           | Quote_loc  -> e
                                                           | _ ->
                                                               failwith
                                                                 "invalid antiquotation"
                                                            in
                                                         let f =
                                                           match aq with
                                                           | "bindings" ->
                                                               generic_antiquote
                                                                 e
                                                           | _ -> give_up ()
                                                            in
                                                         make_list_antiquotation
                                                           _loc Quote_loc f)
                                (Earley.option []
                                   (Earley.fsequence and_kw
                                      (Earley.apply
                                         (fun _default_0  ->
                                            fun _  -> _default_0) let_binding)))))))));
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                pattern)
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   eright_member)
                (Earley.fsequence post_item_attributes
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun l  ->
                                 fun a  ->
                                   fun ((_,(_ty,e)) as erm)  ->
                                     let (_loc_erm,erm) = erm  in
                                     fun pat  ->
                                       let (_loc_pat,pat) = pat  in
                                       let loc = merge2 _loc_pat _loc_erm  in
                                       let (pat,e) =
                                         match _ty with
                                         | None  -> (pat, e)
                                         | Some ty ->
                                             let loc = ghost _loc  in
                                             (pat,
                                               (Exp.constraint_ ~loc e ty))
                                          in
                                       (value_binding
                                          ~attributes:(attach_attrib loc a)
                                          loc pat e)
                                         :: l)
                      (Earley.option []
                         (Earley.fsequence and_kw
                            (Earley.apply
                               (fun _default_0  -> fun _  -> _default_0)
                               let_binding))))));
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                value_name)
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   right_member)
                (Earley.fsequence post_item_attributes
                   (Earley.apply
                      (fun l  ->
                         fun a  ->
                           fun e  ->
                             let (_loc_e,e) = e  in
                             fun vn  ->
                               let (_loc_vn,vn) = vn  in
                               let loc = merge2 _loc_vn _loc_e  in
                               let pat = pat_ident _loc_vn vn  in
                               (value_binding
                                  ~attributes:(attach_attrib loc a) loc pat e)
                                 :: l)
                      (Earley.option []
                         (Earley.fsequence and_kw
                            (Earley.apply
                               (fun _default_0  -> fun _  -> _default_0)
                               let_binding))))));
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                value_name)
             (Earley.fsequence (Earley.char ':' ':')
                (Earley.fsequence only_poly_typexpr
                   (Earley.fsequence (Earley.char '=' '=')
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     fun x  ->
                                       ((locate str pos str' pos'), x))
                            expression)
                         (Earley.fsequence post_item_attributes
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun l  ->
                                          fun a  ->
                                            fun e  ->
                                              let (_loc_e,e) = e  in
                                              fun _  ->
                                                fun ty  ->
                                                  fun _  ->
                                                    fun vn  ->
                                                      let (_loc_vn,vn) = vn
                                                         in
                                                      let pat =
                                                        loc_pat (ghost _loc)
                                                          (Ppat_constraint
                                                             ((loc_pat
                                                                 _loc_vn
                                                                 (Ppat_var
                                                                    (
                                                                    id_loc vn
                                                                    _loc_vn))),
                                                               (loc_typ
                                                                  (ghost _loc)
                                                                  ty.ptyp_desc)))
                                                         in
                                                      let loc =
                                                        merge2 _loc_vn _loc_e
                                                         in
                                                      (value_binding
                                                         ~attributes:(
                                                         attach_attrib loc a)
                                                         loc pat e)
                                                        :: l)
                               (Earley.option []
                                  (Earley.fsequence and_kw
                                     (Earley.apply
                                        (fun _default_0  ->
                                           fun _  -> _default_0) let_binding)))))))));
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                value_name)
             (Earley.fsequence (Earley.char ':' ':')
                (Earley.fsequence poly_syntax_typexpr
                   (Earley.fsequence (Earley.char '=' '=')
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     fun x  ->
                                       ((locate str pos str' pos'), x))
                            expression)
                         (Earley.fsequence post_item_attributes
                            (Earley.apply
                               (fun l  ->
                                  fun a  ->
                                    fun e  ->
                                      let (_loc_e,e) = e  in
                                      fun _  ->
                                        fun ((ids,ty) as _default_0)  ->
                                          fun _  ->
                                            fun vn  ->
                                              let (_loc_vn,vn) = vn  in
                                              let loc = merge2 _loc_vn _loc_e
                                                 in
                                              let (e,ty) =
                                                wrap_type_annotation loc ids
                                                  ty e
                                                 in
                                              let pat =
                                                loc_pat (ghost loc)
                                                  (Ppat_constraint
                                                     ((loc_pat _loc_vn
                                                         (Ppat_var
                                                            (id_loc vn
                                                               _loc_vn))),
                                                       ty))
                                                 in
                                              (value_binding
                                                 ~attributes:(attach_attrib
                                                                loc a) loc
                                                 pat e)
                                                :: l)
                               (Earley.option []
                                  (Earley.fsequence and_kw
                                     (Earley.apply
                                        (fun _default_0  ->
                                           fun _  -> _default_0) let_binding)))))))))])
      
    [@@@ocaml.text " FIXME OCAML: shoud not change the position below "]
    let (match_case,match_case__set__grammar) =
      Earley.grammar_family "match_case" 
    let match_case __curry__varx0 __curry__varx1 =
      match_case (__curry__varx0, __curry__varx1) 
    let _ =
      match_case__set__grammar
        (fun (alm,lvl)  ->
           Earley.fsequence pattern
             (Earley.fsequence
                (Earley.option None
                   (Earley.apply (fun x  -> Some x)
                      (Earley.fsequence when_kw
                         (Earley.apply
                            (fun _default_0  -> fun _  -> _default_0)
                            expression))))
                (Earley.fsequence arrow_re
                   (Earley.apply
                      (fun e  ->
                         fun _default_0  ->
                           fun w  -> fun pat  -> make_case pat e w)
                      (Earley.alternatives
                         [Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun _  -> Exp.unreachable ~loc:_loc ())
                            (Earley.string "." ".");
                         expression_lvl (alm, lvl)])))))
      
    let _ =
      set_grammar match_cases
        (Earley.alternatives
           [Earley.fsequence (Earley.char '$' '$')
              (Earley.fsequence (Earley.no_blank_test ())
                 (Earley.fsequence
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x)
                          (Earley.fsequence (Earley.string "cases" "cases")
                             (Earley.apply (fun _  -> fun _  -> ())
                                (Earley.string ":" ":")))))
                    (Earley.fsequence expression
                       (Earley.fsequence (Earley.no_blank_test ())
                          (Earley.apply_position
                             (fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos
                                         in
                                      fun _  ->
                                        fun _  ->
                                          fun e  ->
                                            fun _default_0  ->
                                              fun _  ->
                                                fun _  ->
                                                  list_antiquotation _loc e)
                             (Earley.char '$' '$'))))));
           Earley.fsequence
             (Earley.option None
                (Earley.apply (fun x  -> Some x) (Earley.char '|' '|')))
             (Earley.fsequence
                (Earley.apply List.rev
                   (Earley.fixpoint []
                      (Earley.apply (fun x  -> fun y  -> x :: y)
                         (Earley.fsequence (match_case Let Seq)
                            (Earley.apply
                               (fun _  -> fun _default_0  -> _default_0)
                               (Earley.char '|' '|'))))))
                (Earley.fsequence (match_case Match Seq)
                   (Earley.apply
                      (fun _default_0  ->
                         fun x  -> fun l  -> fun _default_1  -> l @ [x])
                      no_semi)));
           Earley.apply (fun _  -> []) (Earley.empty ())])
      
    let type_coercion = Earley.declare_grammar "type_coercion" 
    let _ =
      Earley.set_grammar type_coercion
        (Earley.alternatives
           [Earley.fsequence (Earley.string ":>" ":>")
              (Earley.apply (fun t'  -> fun _  -> (None, (Some t'))) typexpr);
           Earley.fsequence (Earley.string ":" ":")
             (Earley.fsequence typexpr
                (Earley.apply (fun t'  -> fun t  -> fun _  -> ((Some t), t'))
                   (Earley.option None
                      (Earley.apply (fun x  -> Some x)
                         (Earley.fsequence (Earley.string ":>" ":>")
                            (Earley.apply (fun t'  -> fun _  -> t') typexpr))))))])
      
    let expression_list = Earley.declare_grammar "expression_list" 
    let _ =
      Earley.set_grammar expression_list
        (Earley.alternatives
           [Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence
             (Earley.apply List.rev
                (Earley.fixpoint []
                   (Earley.apply (fun x  -> fun y  -> x :: y)
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     fun x  ->
                                       ((locate str pos str' pos'), x))
                            (expression_lvl (NoMatch, (next_exp Seq))))
                         (Earley.apply
                            (fun _  ->
                               fun e  -> let (_loc_e,e) = e  in (e, _loc_e))
                            semi_col)))))
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   (expression_lvl (Match, (next_exp Seq))))
                (Earley.apply
                   (fun _default_0  ->
                      fun e  ->
                        let (_loc_e,e) = e  in fun l  -> l @ [(e, _loc_e)])
                   (Earley.option None
                      (Earley.apply (fun x  -> Some x) semi_col))))])
      
    let record_item = Earley.declare_grammar "record_item" 
    let _ =
      Earley.set_grammar record_item
        (Earley.alternatives
           [Earley.apply
              (fun f  ->
                 let (_loc_f,f) = f  in
                 let id = id_loc (Lident f) _loc_f  in
                 (id, (loc_expr _loc_f (Pexp_ident id))))
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x)) lident);
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                field)
             (Earley.fsequence (Earley.char '=' '=')
                (Earley.apply
                   (fun e  ->
                      fun _  ->
                        fun f  ->
                          let (_loc_f,f) = f  in ((id_loc f _loc_f), e))
                   (expression_lvl (NoMatch, (next_exp Seq)))))])
      
    let last_record_item = Earley.declare_grammar "last_record_item" 
    let _ =
      Earley.set_grammar last_record_item
        (Earley.alternatives
           [Earley.apply
              (fun f  ->
                 let (_loc_f,f) = f  in
                 let id = id_loc (Lident f) _loc_f  in
                 (id, (loc_expr _loc_f (Pexp_ident id))))
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x)) lident);
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                field)
             (Earley.fsequence (Earley.char '=' '=')
                (Earley.apply
                   (fun e  ->
                      fun _  ->
                        fun f  ->
                          let (_loc_f,f) = f  in ((id_loc f _loc_f), e))
                   (expression_lvl (Match, (next_exp Seq)))))])
      
    let _ =
      set_grammar record_list
        (Earley.alternatives
           [Earley.apply (fun _  -> []) (Earley.empty ());
           Earley.fsequence
             (Earley.apply List.rev
                (Earley.fixpoint []
                   (Earley.apply (fun x  -> fun y  -> x :: y)
                      (Earley.fsequence record_item
                         (Earley.apply
                            (fun _  -> fun _default_0  -> _default_0)
                            semi_col)))))
             (Earley.fsequence last_record_item
                (Earley.apply
                   (fun _default_0  -> fun it  -> fun l  -> l @ [it])
                   (Earley.option None
                      (Earley.apply (fun x  -> Some x) semi_col))))])
      
    let obj_item = Earley.declare_grammar "obj_item" 
    let _ =
      Earley.set_grammar obj_item
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              inst_var_name)
           (Earley.fsequence (Earley.char '=' '=')
              (Earley.apply
                 (fun e  ->
                    fun _  ->
                      fun v  -> let (_loc_v,v) = v  in ((id_loc v _loc_v), e))
                 (expression_lvl (Match, (next_exp Seq))))))
      
    let class_expr_base = Earley.declare_grammar "class_expr_base" 
    let _ =
      Earley.set_grammar class_expr_base
        (Earley.alternatives
           [Earley.fsequence object_kw
              (Earley.fsequence class_body
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _default_0  ->
                               fun cb  ->
                                 fun _default_1  ->
                                   loc_pcl _loc (Pcl_structure cb)) end_kw));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun cp  ->
                        let (_loc_cp,cp) = cp  in
                        let cp = id_loc cp _loc_cp  in
                        loc_pcl _loc (Pcl_constr (cp, [])))
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                class_path);
           Earley.fsequence (Earley.char '[' '[')
             (Earley.fsequence typexpr
                (Earley.fsequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            (Earley.fsequence (Earley.char ',' ',')
                               (Earley.apply (fun te  -> fun _  -> te)
                                  typexpr)))))
                   (Earley.fsequence (Earley.char ']' ']')
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun cp  ->
                                    let (_loc_cp,cp) = cp  in
                                    fun _  ->
                                      fun tes  ->
                                        fun te  ->
                                          fun _  ->
                                            let cp = id_loc cp _loc_cp  in
                                            loc_pcl _loc
                                              (Pcl_constr (cp, (te :: tes))))
                         (Earley.apply_position
                            (fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     fun x  ->
                                       ((locate str pos str' pos'), x))
                            class_path)))));
           Earley.fsequence (Earley.string "(" "(")
             (Earley.fsequence class_expr
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun _  ->
                              fun ce  -> fun _  -> loc_pcl _loc ce.pcl_desc)
                   (Earley.string ")" ")")));
           Earley.fsequence (Earley.string "(" "(")
             (Earley.fsequence class_expr
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.fsequence class_type
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun _  ->
                                    fun ct  ->
                                      fun _  ->
                                        fun ce  ->
                                          fun _  ->
                                            loc_pcl _loc
                                              (Pcl_constraint (ce, ct)))
                         (Earley.string ")" ")")))));
           Earley.fsequence fun_kw
             (Earley.fsequence
                (Earley.apply List.rev
                   (Earley.fixpoint1 []
                      (Earley.apply (fun x  -> fun y  -> x :: y)
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun p  -> (p, _loc)) (parameter false)))))
                (Earley.fsequence arrow_re
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun ce  ->
                                 fun _default_0  ->
                                   fun ps  ->
                                     fun _default_1  ->
                                       apply_params_cls _loc ps ce)
                      class_expr)));
           Earley.fsequence let_kw
             (Earley.fsequence rec_flag
                (Earley.fsequence let_binding
                   (Earley.fsequence in_kw
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun ce  ->
                                    fun _default_0  ->
                                      fun lbs  ->
                                        fun r  ->
                                          fun _default_1  ->
                                            loc_pcl _loc
                                              (Pcl_let (r, lbs, ce)))
                         class_expr))))])
      
    let _ =
      set_grammar class_expr
        (Earley.fsequence class_expr_base
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun args  ->
                         fun ce  ->
                           match args with
                           | None  -> ce
                           | Some l -> loc_pcl _loc (Pcl_apply (ce, l)))
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.apply List.rev
                       (Earley.fixpoint1 []
                          (Earley.apply (fun x  -> fun y  -> x :: y) argument)))))))
      
    let class_field = Earley.declare_grammar "class_field" 
    let _ =
      Earley.set_grammar class_field
        (Earley.alternatives
           [Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun ((s,l) as _default_0)  ->
                         loc_pcf _loc (Pcf_extension (s, l)))
              floating_extension;
           Earley.fsequence inherit_kw
             (Earley.fsequence override_flag
                (Earley.fsequence class_expr
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun id  ->
                                 fun ce  ->
                                   fun o  ->
                                     fun _default_0  ->
                                       loc_pcf _loc (Pcf_inherit (o, ce, id)))
                      (Earley.option None
                         (Earley.apply (fun x  -> Some x)
                            (Earley.fsequence as_kw
                               (Earley.apply
                                  (fun _default_0  -> fun _  -> _default_0)
                                  lident)))))));
           Earley.fsequence val_kw
             (Earley.fsequence override_flag
                (Earley.fsequence mutable_flag
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  ->
                                  fun x  -> ((locate str pos str' pos'), x))
                         inst_var_name)
                      (Earley.fsequence
                         (Earley.option None
                            (Earley.apply (fun x  -> Some x)
                               (Earley.fsequence (Earley.char ':' ':')
                                  (Earley.apply (fun t  -> fun _  -> t)
                                     typexpr))))
                         (Earley.fsequence (Earley.char '=' '=')
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun e  ->
                                          fun _  ->
                                            fun te  ->
                                              fun ivn  ->
                                                let (_loc_ivn,ivn) = ivn  in
                                                fun m  ->
                                                  fun o  ->
                                                    fun _default_0  ->
                                                      let ivn =
                                                        id_loc ivn _loc_ivn
                                                         in
                                                      let ex =
                                                        match te with
                                                        | None  -> e
                                                        | Some t ->
                                                            loc_expr
                                                              (ghost
                                                                 (merge2
                                                                    _loc_ivn
                                                                    _loc))
                                                              (pexp_constraint
                                                                 (e, t))
                                                         in
                                                      loc_pcf _loc
                                                        (Pcf_val
                                                           (ivn, m,
                                                             (Cfk_concrete
                                                                (o, ex)))))
                               expression))))));
           Earley.fsequence val_kw
             (Earley.fsequence mutable_flag
                (Earley.fsequence virtual_kw
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  ->
                                  fun x  -> ((locate str pos str' pos'), x))
                         inst_var_name)
                      (Earley.fsequence (Earley.string ":" ":")
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun te  ->
                                       fun _  ->
                                         fun ivn  ->
                                           let (_loc_ivn,ivn) = ivn  in
                                           fun _default_0  ->
                                             fun m  ->
                                               fun _default_1  ->
                                                 let ivn =
                                                   id_loc ivn _loc_ivn  in
                                                 loc_pcf _loc
                                                   (Pcf_val
                                                      (ivn, m,
                                                        (Cfk_virtual te))))
                            typexpr)))));
           Earley.fsequence val_kw
             (Earley.fsequence virtual_kw
                (Earley.fsequence mutable_kw
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  ->
                                  fun x  -> ((locate str pos str' pos'), x))
                         inst_var_name)
                      (Earley.fsequence (Earley.string ":" ":")
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun te  ->
                                       fun _  ->
                                         fun ivn  ->
                                           let (_loc_ivn,ivn) = ivn  in
                                           fun _default_0  ->
                                             fun _default_1  ->
                                               fun _default_2  ->
                                                 let ivn =
                                                   id_loc ivn _loc_ivn  in
                                                 loc_pcf _loc
                                                   (Pcf_val
                                                      (ivn, Mutable,
                                                        (Cfk_virtual te))))
                            typexpr)))));
           Earley.fsequence method_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   (Earley.fsequence override_flag
                      (Earley.fsequence private_flag
                         (Earley.apply
                            (fun _default_0  ->
                               fun _default_1  ->
                                 fun _default_2  ->
                                   (_default_2, _default_1, _default_0))
                            method_name))))
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.fsequence poly_typexpr
                      (Earley.fsequence (Earley.char '=' '=')
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun e  ->
                                       fun _  ->
                                         fun te  ->
                                           fun _  ->
                                             fun ((_,(o,p,mn)) as t)  ->
                                               let (_loc_t,t) = t  in
                                               fun _default_0  ->
                                                 let e =
                                                   loc_expr
                                                     (ghost
                                                        (merge2 _loc_t _loc))
                                                     (Pexp_poly
                                                        (e, (Some te)))
                                                    in
                                                 loc_pcf _loc
                                                   (Pcf_method
                                                      (mn, p,
                                                        (Cfk_concrete (o, e)))))
                            expression)))));
           Earley.fsequence method_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   (Earley.fsequence override_flag
                      (Earley.fsequence private_flag
                         (Earley.apply
                            (fun _default_0  ->
                               fun _default_1  ->
                                 fun _default_2  ->
                                   (_default_2, _default_1, _default_0))
                            method_name))))
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.fsequence poly_syntax_typexpr
                      (Earley.fsequence (Earley.char '=' '=')
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun e  ->
                                       let (_loc_e,e) = e  in
                                       fun _  ->
                                         fun ((ids,te) as _default_0)  ->
                                           fun _  ->
                                             fun ((_,(o,p,mn)) as t)  ->
                                               let (_loc_t,t) = t  in
                                               fun _default_1  ->
                                                 let _loc_e =
                                                   merge2 _loc_t _loc  in
                                                 let (e,poly) =
                                                   wrap_type_annotation
                                                     _loc_e ids te e
                                                    in
                                                 let e =
                                                   loc_expr (ghost _loc_e)
                                                     (Pexp_poly
                                                        (e, (Some poly)))
                                                    in
                                                 loc_pcf _loc
                                                   (Pcf_method
                                                      (mn, p,
                                                        (Cfk_concrete (o, e)))))
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               expression))))));
           Earley.fsequence method_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   (Earley.fsequence override_flag
                      (Earley.fsequence private_flag
                         (Earley.apply
                            (fun _default_0  ->
                               fun _default_1  ->
                                 fun _default_2  ->
                                   (_default_2, _default_1, _default_0))
                            method_name))))
                (Earley.fsequence
                   (Earley.apply List.rev
                      (Earley.fixpoint []
                         (Earley.apply (fun x  -> fun y  -> x :: y)
                            (Earley.apply
                               (fun p  -> let (_loc_p,p) = p  in (p, _loc_p))
                               (Earley.apply_position
                                  (fun str  ->
                                     fun pos  ->
                                       fun str'  ->
                                         fun pos'  ->
                                           fun x  ->
                                             ((locate str pos str' pos'), x))
                                  (parameter true))))))
                   (Earley.fsequence
                      (Earley.apply_position
                         (fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  ->
                                  fun x  -> ((locate str pos str' pos'), x))
                         (Earley.option None
                            (Earley.apply (fun x  -> Some x)
                               (Earley.fsequence (Earley.string ":" ":")
                                  (Earley.apply (fun te  -> fun _  -> te)
                                     typexpr)))))
                      (Earley.fsequence (Earley.char '=' '=')
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun e  ->
                                       let (_loc_e,e) = e  in
                                       fun _  ->
                                         fun te  ->
                                           let (_loc_te,te) = te  in
                                           fun ps  ->
                                             fun ((_,(o,p,mn)) as t)  ->
                                               let (_loc_t,t) = t  in
                                               fun _default_0  ->
                                                 if (ps = []) && (te <> None)
                                                 then give_up ();
                                                 (let e =
                                                    match te with
                                                    | None  -> e
                                                    | Some te ->
                                                        loc_expr
                                                          (ghost
                                                             (merge2 _loc_te
                                                                _loc_e))
                                                          (pexp_constraint
                                                             (e, te))
                                                     in
                                                  let e : expression =
                                                    apply_params ~gh:true
                                                      _loc_e ps e
                                                     in
                                                  let e =
                                                    loc_expr
                                                      (ghost
                                                         (merge2 _loc_t
                                                            _loc_e))
                                                      (Pexp_poly (e, None))
                                                     in
                                                  loc_pcf _loc
                                                    (Pcf_method
                                                       (mn, p,
                                                         (Cfk_concrete (o, e))))))
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               expression))))));
           Earley.fsequence method_kw
             (Earley.fsequence private_flag
                (Earley.fsequence virtual_kw
                   (Earley.fsequence method_name
                      (Earley.fsequence (Earley.string ":" ":")
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun pte  ->
                                       fun _  ->
                                         fun mn  ->
                                           fun _default_0  ->
                                             fun p  ->
                                               fun _default_1  ->
                                                 loc_pcf _loc
                                                   (Pcf_method
                                                      (mn, p,
                                                        (Cfk_virtual pte))))
                            poly_typexpr)))));
           Earley.fsequence method_kw
             (Earley.fsequence virtual_kw
                (Earley.fsequence private_kw
                   (Earley.fsequence method_name
                      (Earley.fsequence (Earley.string ":" ":")
                         (Earley.apply_position
                            (fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos
                                        in
                                     fun pte  ->
                                       fun _  ->
                                         fun mn  ->
                                           fun _default_0  ->
                                             fun _default_1  ->
                                               fun _default_2  ->
                                                 loc_pcf _loc
                                                   (Pcf_method
                                                      (mn, Private,
                                                        (Cfk_virtual pte))))
                            poly_typexpr)))));
           Earley.fsequence constraint_kw
             (Earley.fsequence typexpr
                (Earley.fsequence (Earley.char '=' '=')
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun te'  ->
                                 fun _  ->
                                   fun te  ->
                                     fun _default_0  ->
                                       loc_pcf _loc
                                         (Pcf_constraint (te, te'))) typexpr)));
           Earley.fsequence initializer_kw
             (Earley.apply_position
                (fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos
                            in
                         fun e  ->
                           fun _default_0  ->
                             loc_pcf _loc (Pcf_initializer e)) expression);
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ((s,l) as _default_0)  ->
                        loc_pcf _loc (Pcf_attribute (s, l)))
             floating_attribute])
      
    let _ =
      set_grammar class_body
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              (Earley.option None (Earley.apply (fun x  -> Some x) pattern)))
           (Earley.apply
              (fun f  ->
                 fun p  ->
                   let (_loc_p,p) = p  in
                   let p =
                     match p with
                     | None  -> loc_pat (ghost _loc_p) Ppat_any
                     | Some p -> p  in
                   { pcstr_self = p; pcstr_fields = f })
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y) class_field)))))
      
    let class_binding = Earley.declare_grammar "class_binding" 
    let _ =
      Earley.set_grammar class_binding
        (Earley.fsequence virtual_flag
           (Earley.fsequence
              (Earley.option []
                 (Earley.fsequence (Earley.string "[" "[")
                    (Earley.fsequence type_parameters
                       (Earley.apply
                          (fun _  -> fun params  -> fun _  -> params)
                          (Earley.string "]" "]")))))
              (Earley.fsequence
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    class_name)
                 (Earley.fsequence
                    (Earley.apply_position
                       (fun str  ->
                          fun pos  ->
                            fun str'  ->
                              fun pos'  ->
                                fun x  -> ((locate str pos str' pos'), x))
                       (Earley.apply List.rev
                          (Earley.fixpoint []
                             (Earley.apply (fun x  -> fun y  -> x :: y)
                                (Earley.apply_position
                                   (fun __loc__start__buf  ->
                                      fun __loc__start__pos  ->
                                        fun __loc__end__buf  ->
                                          fun __loc__end__pos  ->
                                            let _loc =
                                              locate __loc__start__buf
                                                __loc__start__pos
                                                __loc__end__buf
                                                __loc__end__pos
                                               in
                                            fun p  -> (p, _loc))
                                   (parameter false))))))
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x)
                             (Earley.fsequence (Earley.string ":" ":")
                                (Earley.apply (fun ct  -> fun _  -> ct)
                                   class_type))))
                       (Earley.fsequence (Earley.char '=' '=')
                          (Earley.apply_position
                             (fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos
                                         in
                                      fun ce  ->
                                        fun _  ->
                                          fun ct  ->
                                            fun ps  ->
                                              let (_loc_ps,ps) = ps  in
                                              fun cn  ->
                                                let (_loc_cn,cn) = cn  in
                                                fun params  ->
                                                  fun v  ->
                                                    let ce =
                                                      apply_params_cls
                                                        ~gh:true
                                                        (merge2 _loc_ps _loc)
                                                        ps ce
                                                       in
                                                    let ce =
                                                      match ct with
                                                      | None  -> ce
                                                      | Some ct ->
                                                          loc_pcl _loc
                                                            (Pcl_constraint
                                                               (ce, ct))
                                                       in
                                                    fun _loc  ->
                                                      class_type_declaration
                                                        ~attributes:(
                                                        attach_attrib _loc [])
                                                        _loc
                                                        (id_loc cn _loc_cn)
                                                        params v ce)
                             class_expr)))))))
      
    let class_definition = Earley.declare_grammar "class_definition" 
    let _ =
      Earley.set_grammar class_definition
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              class_kw)
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 class_binding)
              (Earley.apply
                 (fun cbs  ->
                    fun cb  ->
                      let (_loc_cb,cb) = cb  in
                      fun k  ->
                        let (_loc_k,k) = k  in (cb (merge2 _loc_k _loc_cb))
                          :: cbs)
                 (Earley.apply List.rev
                    (Earley.fixpoint []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          (Earley.fsequence and_kw
                             (Earley.apply_position
                                (fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos
                                            in
                                         fun cb  -> fun _  -> cb _loc)
                                class_binding))))))))
      
    let pexp_list _loc ?loc_cl  l =
      if l = []
      then loc_expr _loc (pexp_construct ((id_loc (Lident "[]") _loc), None))
      else
        (let loc_cl =
           ghost (match loc_cl with | None  -> _loc | Some pos -> pos)  in
         List.fold_right
           (fun (x,pos)  ->
              fun acc  ->
                let _loc = ghost (merge2 pos loc_cl)  in
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
        | Some e -> e  in
      (lbl, e) 
    let rec mk_seq loc_c final =
      function
      | [] -> final
      | x::l ->
          let res = mk_seq loc_c final l  in
          loc_expr (merge2 x.pexp_loc loc_c) (Pexp_sequence (x, res))
      
    let (extra_expressions_grammar,extra_expressions_grammar__set__grammar) =
      Earley.grammar_family "extra_expressions_grammar" 
    let _ =
      extra_expressions_grammar__set__grammar
        (fun c  -> alternatives (List.map (fun g  -> g c) extra_expressions))
      
    let structure_item_simple = declare_grammar "structure_item_simple" 
    let (left_expr,left_expr__set__grammar) = Earley.grammar_prio "left_expr" 
    let (prefix_expr,prefix_expr__set__grammar) =
      Earley.grammar_family "prefix_expr" 
    let rec infix_expr lvl =
      if (assoc lvl) = Left
      then
        Earley.fsequence (expression_lvl (NoMatch, lvl))
          (Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun op  ->
                        let (_loc_op,op) = op  in
                        fun e'  ->
                          ((next_exp lvl), false,
                            (fun e  ->
                               fun (_loc,_)  ->
                                 mk_binary_op _loc e' op _loc_op e)))
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                (infix_symbol lvl)))
      else
        if (assoc lvl) = NoAssoc
        then
          Earley.fsequence (expression_lvl (NoMatch, (next_exp lvl)))
            (Earley.apply_position
               (fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos
                           in
                        fun op  ->
                          let (_loc_op,op) = op  in
                          fun e'  ->
                            ((next_exp lvl), false,
                              (fun e  ->
                                 fun (_loc,_)  ->
                                   mk_binary_op _loc e' op _loc_op e)))
               (Earley.apply_position
                  (fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  ->
                           fun x  -> ((locate str pos str' pos'), x))
                  (infix_symbol lvl)))
        else
          Earley.apply_position
            (fun __loc__start__buf  ->
               fun __loc__start__pos  ->
                 fun __loc__end__buf  ->
                   fun __loc__end__pos  ->
                     let _loc =
                       locate __loc__start__buf __loc__start__pos
                         __loc__end__buf __loc__end__pos
                        in
                     fun ls  ->
                       ((next_exp lvl), false,
                         (fun e  ->
                            fun (_loc,_)  ->
                              List.fold_right
                                (fun (_loc_e,e',op,_loc_op)  ->
                                   fun acc  ->
                                     mk_binary_op (merge2 _loc_e _loc) e' op
                                       _loc_op acc) ls e)))
            (Earley.apply List.rev
               (Earley.fixpoint1 []
                  (Earley.apply (fun x  -> fun y  -> x :: y)
                     (Earley.fsequence
                        (expression_lvl (NoMatch, (next_exp lvl)))
                        (Earley.apply_position
                           (fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos
                                       in
                                    fun op  ->
                                      let (_loc_op,op) = op  in
                                      fun e'  -> (_loc, e', op, _loc_op))
                           (Earley.apply_position
                              (fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       fun x  ->
                                         ((locate str pos str' pos'), x))
                              (infix_symbol lvl)))))))
      
    let _ =
      left_expr__set__grammar
        ([(((fun (alm,lvl)  -> lvl <= Pow)), (infix_expr Pow));
         (((fun (alm,lvl)  -> (allow_let alm) && (lvl < App))),
           (Earley.fsequence fun_kw
              (Earley.fsequence
                 (Earley.apply List.rev
                    (Earley.fixpoint []
                       (Earley.apply (fun x  -> fun y  -> x :: y)
                          (Earley.apply
                             (fun lbl  ->
                                let (_loc_lbl,lbl) = lbl  in (lbl, _loc_lbl))
                             (Earley.apply_position
                                (fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         fun x  ->
                                           ((locate str pos str' pos'), x))
                                (parameter true))))))
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _default_0  ->
                               fun l  ->
                                 fun _default_1  ->
                                   (Seq, false,
                                     (fun e  ->
                                        fun (_loc,_)  ->
                                          loc_expr _loc
                                            (apply_params _loc l e).pexp_desc)))
                    arrow_re))));
         (((fun (alm,lvl)  -> (allow_let alm) && (lvl < App))),
           (Earley.fsequence let_kw
              (Earley.fsequence
                 (Earley.alternatives
                    [Earley.fsequence open_kw
                       (Earley.fsequence override_flag
                          (Earley.apply_position
                             (fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos
                                         in
                                      fun mp  ->
                                        let (_loc_mp,mp) = mp  in
                                        fun o  ->
                                          fun _default_0  ->
                                            fun e  ->
                                              fun (_loc,_)  ->
                                                let mp = id_loc mp _loc_mp
                                                   in
                                                loc_expr _loc
                                                  (Pexp_open (o, mp, e)))
                             (Earley.apply_position
                                (fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         fun x  ->
                                           ((locate str pos str' pos'), x))
                                module_path)));
                    Earley.fsequence rec_flag
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun l  ->
                                    fun r  ->
                                      fun e  ->
                                        fun (_loc,_)  ->
                                          loc_expr _loc (Pexp_let (r, l, e)))
                         let_binding);
                    Earley.fsequence module_kw
                      (Earley.fsequence module_name
                         (Earley.fsequence
                            (Earley.apply List.rev
                               (Earley.fixpoint []
                                  (Earley.apply (fun x  -> fun y  -> x :: y)
                                     (Earley.fsequence (Earley.char '(' '(')
                                        (Earley.fsequence module_name
                                           (Earley.fsequence
                                              (Earley.option None
                                                 (Earley.apply
                                                    (fun x  -> Some x)
                                                    (Earley.fsequence
                                                       (Earley.char ':' ':')
                                                       (Earley.apply
                                                          (fun _default_0  ->
                                                             fun _  ->
                                                               _default_0)
                                                          module_type))))
                                              (Earley.apply_position
                                                 (fun __loc__start__buf  ->
                                                    fun __loc__start__pos  ->
                                                      fun __loc__end__buf  ->
                                                        fun __loc__end__pos 
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos
                                                             in
                                                          fun _  ->
                                                            fun mt  ->
                                                              fun mn  ->
                                                                fun _  ->
                                                                  (mn, mt,
                                                                    _loc))
                                                 (Earley.char ')' ')'))))))))
                            (Earley.fsequence
                               (Earley.apply_position
                                  (fun str  ->
                                     fun pos  ->
                                       fun str'  ->
                                         fun pos'  ->
                                           fun x  ->
                                             ((locate str pos str' pos'), x))
                                  (Earley.option None
                                     (Earley.apply (fun x  -> Some x)
                                        (Earley.fsequence
                                           (Earley.string ":" ":")
                                           (Earley.apply
                                              (fun mt  -> fun _  -> mt)
                                              module_type)))))
                               (Earley.fsequence (Earley.string "=" "=")
                                  (Earley.apply_position
                                     (fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos
                                                 in
                                              fun me  ->
                                                let (_loc_me,me) = me  in
                                                fun _  ->
                                                  fun mt  ->
                                                    let (_loc_mt,mt) = mt  in
                                                    fun l  ->
                                                      fun mn  ->
                                                        fun _default_0  ->
                                                          fun e  ->
                                                            fun (_loc,_)  ->
                                                              let me =
                                                                match mt with
                                                                | None  -> me
                                                                | Some mt ->
                                                                    mexpr_loc
                                                                    (merge2
                                                                    _loc_mt
                                                                    _loc_me)
                                                                    (Pmod_constraint
                                                                    (me, mt))
                                                                 in
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
                                                                  (List.rev l)
                                                                 in
                                                              loc_expr _loc
                                                                (Pexp_letmodule
                                                                   (mn, me,
                                                                    e)))
                                     (Earley.apply_position
                                        (fun str  ->
                                           fun pos  ->
                                             fun str'  ->
                                               fun pos'  ->
                                                 fun x  ->
                                                   ((locate str pos str' pos'),
                                                     x)) module_expr))))))])
                 (Earley.apply
                    (fun _  -> fun f  -> fun _  -> (Seq, false, f)) in_kw))));
         (((fun (alm,lvl)  -> ((allow_let alm) || (lvl = If)) && (lvl < App))),
           (Earley.fsequence if_kw
              (Earley.fsequence expression
                 (Earley.fsequence then_kw
                    (Earley.fsequence
                       (expression_lvl (Match, (next_exp Seq)))
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _default_0  ->
                                     fun e  ->
                                       fun _default_1  ->
                                         fun c  ->
                                           fun _default_2  ->
                                             ((next_exp Seq), false,
                                               (fun e'  ->
                                                  fun (_loc,_)  ->
                                                    {
                                                      Parsetree.pexp_desc =
                                                        (Parsetree.Pexp_ifthenelse
                                                           (c, e, (Some e')));
                                                      Parsetree.pexp_loc =
                                                        _loc;
                                                      Parsetree.pexp_attributes
                                                        = []
                                                    }))) else_kw))))));
         (((fun (alm,lvl)  -> ((allow_let alm) || (lvl = If)) && (lvl < App))),
           (Earley.fsequence if_kw
              (Earley.fsequence expression
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _default_0  ->
                               fun c  ->
                                 fun _default_1  ->
                                   ((next_exp Seq), true,
                                     (fun e  ->
                                        fun (_loc,_)  ->
                                          {
                                            Parsetree.pexp_desc =
                                              (Parsetree.Pexp_ifthenelse
                                                 (c, e, None));
                                            Parsetree.pexp_loc = _loc;
                                            Parsetree.pexp_attributes = []
                                          }))) then_kw))));
         (((fun (alm,lvl)  -> lvl <= Seq)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun ls  ->
                         ((next_exp Seq), false,
                           (fun e'  -> fun (_,_loc)  -> mk_seq _loc e' ls)))
              (Earley.apply List.rev
                 (Earley.fixpoint1 []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.fsequence
                          (expression_lvl (NoMatch, (next_exp Seq)))
                          (Earley.apply
                             (fun _  -> fun _default_0  -> _default_0)
                             semi_col)))))));
         (((fun (alm,lvl)  -> lvl <= Aff)),
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 inst_var_name)
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun _  ->
                            fun v  ->
                              let (_loc_v,v) = v  in
                              ((next_exp Aff), false,
                                (fun e  ->
                                   fun (_loc,_)  ->
                                     loc_expr _loc
                                       (Pexp_setinstvar
                                          ((id_loc v _loc_v), e)))))
                 (Earley.string "<-" "<-"))));
         (((fun (alm,lvl)  -> lvl <= Aff)),
           (Earley.fsequence (expression_lvl (NoMatch, Dot))
              (Earley.fsequence (Earley.char '.' '.')
                 (Earley.fsequence
                    (Earley.alternatives
                       [Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun f  ->
                                     let (_loc_f,f) = f  in
                                     fun e'  ->
                                       fun e  ->
                                         fun (_loc,_)  ->
                                           let f = id_loc f _loc_f  in
                                           loc_expr _loc
                                             (Pexp_setfield (e', f, e)))
                          (Earley.apply_position
                             (fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      fun x  ->
                                        ((locate str pos str' pos'), x))
                             field);
                       Earley.fsequence (Earley.string "(" "(")
                         (Earley.fsequence expression
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun f  ->
                                            fun _  ->
                                              fun e'  ->
                                                fun e  ->
                                                  fun (_loc,_)  ->
                                                    exp_apply _loc
                                                      (array_function
                                                         (ghost
                                                            (merge2
                                                               e'.pexp_loc
                                                               _loc)) "Array"
                                                         "set") [e'; f; e])
                               (Earley.string ")" ")")));
                       Earley.fsequence (Earley.string "[" "[")
                         (Earley.fsequence expression
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun f  ->
                                            fun _  ->
                                              fun e'  ->
                                                fun e  ->
                                                  fun (_loc,_)  ->
                                                    exp_apply _loc
                                                      (array_function
                                                         (ghost
                                                            (merge2
                                                               e'.pexp_loc
                                                               _loc))
                                                         "String" "set")
                                                      [e'; f; e])
                               (Earley.string "]" "]")));
                       Earley.fsequence (Earley.string "{" "{")
                         (Earley.fsequence expression
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun f  ->
                                            fun _  ->
                                              fun e'  ->
                                                fun e  ->
                                                  fun (_loc,_)  ->
                                                    de_ghost
                                                      (bigarray_set
                                                         (ghost
                                                            (merge2
                                                               e'.pexp_loc
                                                               _loc)) e' f e))
                               (Earley.string "}" "}")))])
                    (Earley.apply
                       (fun _  ->
                          fun f  ->
                            fun _  ->
                              fun e'  -> ((next_exp Aff), false, (f e')))
                       (Earley.string "<-" "<-"))))));
         (((fun (alm,lvl)  -> lvl <= Tupl)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun l  ->
                         ((next_exp Tupl), false,
                           (fun e'  ->
                              fun (_loc,_)  -> Exp.tuple ~loc:_loc (l @ [e']))))
              (Earley.apply List.rev
                 (Earley.fixpoint1 []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.fsequence
                          (expression_lvl (NoMatch, (next_exp Tupl)))
                          (Earley.apply
                             (fun _  -> fun _default_0  -> _default_0)
                             (Earley.char ',' ','))))))));
         (((fun (alm,lvl)  -> lvl <= App)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun _default_0  ->
                         ((next_exp App), false,
                           (fun e  ->
                              fun (_loc,_)  -> loc_expr _loc (Pexp_assert e))))
              assert_kw));
         (((fun (alm,lvl)  -> lvl <= App)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun _default_0  ->
                         ((next_exp App), false,
                           (fun e  ->
                              fun (_loc,_)  -> loc_expr _loc (Pexp_lazy e))))
              lazy_kw));
         (((fun (alm,lvl)  -> lvl <= Opp)), (prefix_expr Opp));
         (((fun (alm,lvl)  -> lvl <= Prefix)), (prefix_expr Prefix));
         (((fun (alm,lvl)  -> lvl <= Prod)), (infix_expr Prod));
         (((fun (alm,lvl)  -> lvl <= Sum)), (infix_expr Sum));
         (((fun (alm,lvl)  -> lvl <= Append)), (infix_expr Append));
         (((fun (alm,lvl)  -> lvl <= Cons)), (infix_expr Cons));
         (((fun (alm,lvl)  -> lvl <= Aff)), (infix_expr Aff));
         (((fun (alm,lvl)  -> lvl <= Eq)), (infix_expr Eq));
         (((fun (alm,lvl)  -> lvl <= Conj)), (infix_expr Conj));
         (((fun (alm,lvl)  -> lvl <= Disj)), (infix_expr Disj))],
          (fun (alm,lvl)  -> []))
      
    let _ =
      prefix_expr__set__grammar
        (fun lvl  ->
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun p  ->
                        let (_loc_p,p) = p  in
                        (lvl, false,
                          (fun e  ->
                             fun (_loc,_)  -> mk_unary_op _loc p _loc_p e)))
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                (prefix_symbol lvl)))
      
    let prefix_expression = Earley.declare_grammar "prefix_expression" 
    let _ =
      Earley.set_grammar prefix_expression
        (Earley.alternatives
           [alternatives extra_prefix_expressions;
           Earley.fsequence function_kw
             (Earley.apply_position
                (fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos
                            in
                         fun l  ->
                           fun _default_0  ->
                             {
                               Parsetree.pexp_desc =
                                 (Parsetree.Pexp_function l);
                               Parsetree.pexp_loc = _loc;
                               Parsetree.pexp_attributes = []
                             }) match_cases);
           Earley.fsequence match_kw
             (Earley.fsequence expression
                (Earley.fsequence with_kw
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun l  ->
                                 fun _default_0  ->
                                   fun e  ->
                                     fun _default_1  ->
                                       {
                                         Parsetree.pexp_desc =
                                           (Parsetree.Pexp_match (e, l));
                                         Parsetree.pexp_loc = _loc;
                                         Parsetree.pexp_attributes = []
                                       }) match_cases)));
           Earley.fsequence try_kw
             (Earley.fsequence expression
                (Earley.fsequence with_kw
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun l  ->
                                 fun _default_0  ->
                                   fun e  ->
                                     fun _default_1  ->
                                       {
                                         Parsetree.pexp_desc =
                                           (Parsetree.Pexp_try (e, l));
                                         Parsetree.pexp_loc = _loc;
                                         Parsetree.pexp_attributes = []
                                       }) match_cases)))])
      
    let (right_expression,right_expression__set__grammar) =
      Earley.grammar_prio "right_expression" 
    let _ =
      right_expression__set__grammar
        ([(((fun lvl  -> lvl <= Atom)),
            (Earley.fsequence (Earley.char '$' '$')
               (Earley.fsequence (Earley.no_blank_test ())
                  (Earley.fsequence
                     (Earley.option "expr"
                        (Earley.fsequence
                           (EarleyStr.regexp ~name:"[a-z]+" "[a-z]+"
                              (fun groupe  -> groupe 0))
                           (Earley.fsequence (Earley.no_blank_test ())
                              (Earley.apply
                                 (fun _  ->
                                    fun _  -> fun _default_0  -> _default_0)
                                 (Earley.char ':' ':')))))
                     (Earley.fsequence expression
                        (Earley.fsequence (Earley.no_blank_test ())
                           (Earley.apply_position
                              (fun __loc__start__buf  ->
                                 fun __loc__start__pos  ->
                                   fun __loc__end__buf  ->
                                     fun __loc__end__pos  ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos
                                          in
                                       fun _  ->
                                         fun _  ->
                                           fun e  ->
                                             fun aq  ->
                                               fun _  ->
                                                 fun _  ->
                                                   let f =
                                                     let open Quote in
                                                       let e_loc =
                                                         exp_ident _loc
                                                           "_loc"
                                                          in
                                                       let locate _loc e =
                                                         quote_record e_loc
                                                           _loc
                                                           [((parsetree
                                                                "pexp_desc"),
                                                              e);
                                                           ((parsetree
                                                               "pexp_loc"),
                                                             (quote_location_t
                                                                e_loc _loc
                                                                _loc));
                                                           ((parsetree
                                                               "pexp_attributes"),
                                                             (quote_attributes
                                                                e_loc _loc []))]
                                                          in
                                                       let generic_antiquote
                                                         e =
                                                         function
                                                         | Quote_pexp  -> e
                                                         | _ ->
                                                             failwith
                                                               "Bad antiquotation..."
                                                          in
                                                       let quote_loc _loc e =
                                                         quote_record e_loc
                                                           _loc
                                                           [((Ldot
                                                                ((Lident
                                                                    "Asttypes"),
                                                                  "txt")), e);
                                                           ((Ldot
                                                               ((Lident
                                                                   "Asttypes"),
                                                                 "loc")),
                                                             (quote_location_t
                                                                e_loc _loc
                                                                _loc))]
                                                          in
                                                       match aq with
                                                       | "expr" ->
                                                           generic_antiquote
                                                             e
                                                       | "longident" ->
                                                           let e =
                                                             quote_const
                                                               e_loc _loc
                                                               (parsetree
                                                                  "Pexp_ident")
                                                               [quote_loc
                                                                  _loc e]
                                                              in
                                                           generic_antiquote
                                                             (locate _loc e)
                                                       | "bool" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_bool")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "int" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_int")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "float" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_float")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "string" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_string")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "char" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_char")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "list" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_list")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "tuple" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_tuple")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | "array" ->
                                                           generic_antiquote
                                                             (quote_apply
                                                                e_loc _loc
                                                                (pa_ast
                                                                   "exp_array")
                                                                [quote_location_t
                                                                   e_loc _loc
                                                                   _loc;
                                                                e])
                                                       | _ -> give_up ()
                                                      in
                                                   Quote.pexp_antiquotation
                                                     _loc f)
                              (Earley.char '$' '$'))))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun id  ->
                         let (_loc_id,id) = id  in
                         loc_expr _loc (Pexp_ident (id_loc id _loc_id)))
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 value_path)));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun c  -> loc_expr _loc (Pexp_constant c)) constant));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 module_path)
              (Earley.fsequence (Earley.string "." ".")
                 (Earley.fsequence (Earley.string "(" "(")
                    (Earley.fsequence expression
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _  ->
                                     fun e  ->
                                       fun _  ->
                                         fun _  ->
                                           fun mp  ->
                                             let (_loc_mp,mp) = mp  in
                                             let mp = id_loc mp _loc_mp  in
                                             loc_expr _loc
                                               (Pexp_open (Fresh, mp, e)))
                          (Earley.string ")" ")")))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 module_path)
              (Earley.fsequence (Earley.char '.' '.')
                 (Earley.fsequence (Earley.char '[' '[')
                    (Earley.fsequence expression_list
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun cl  ->
                                     let (_loc_cl,cl) = cl  in
                                     fun l  ->
                                       fun _  ->
                                         fun _  ->
                                           fun mp  ->
                                             let (_loc_mp,mp) = mp  in
                                             let mp = id_loc mp _loc_mp  in
                                             loc_expr _loc
                                               (Pexp_open
                                                  (Fresh, mp,
                                                    (loc_expr _loc
                                                       (pexp_list _loc
                                                          ~loc_cl:_loc_cl l).pexp_desc))))
                          (Earley.apply_position
                             (fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      fun x  ->
                                        ((locate str pos str' pos'), x))
                             (Earley.char ']' ']'))))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 module_path)
              (Earley.fsequence (Earley.char '.' '.')
                 (Earley.fsequence (Earley.char '{' '{')
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x)
                             (Earley.fsequence expression
                                (Earley.apply
                                   (fun _  -> fun _default_0  -> _default_0)
                                   with_kw))))
                       (Earley.fsequence record_list
                          (Earley.apply_position
                             (fun __loc__start__buf  ->
                                fun __loc__start__pos  ->
                                  fun __loc__end__buf  ->
                                    fun __loc__end__pos  ->
                                      let _loc =
                                        locate __loc__start__buf
                                          __loc__start__pos __loc__end__buf
                                          __loc__end__pos
                                         in
                                      fun _  ->
                                        fun l  ->
                                          fun e  ->
                                            fun _  ->
                                              fun _  ->
                                                fun mp  ->
                                                  let (_loc_mp,mp) = mp  in
                                                  let mp = id_loc mp _loc_mp
                                                     in
                                                  loc_expr _loc
                                                    (Pexp_open
                                                       (Fresh, mp,
                                                         (loc_expr _loc
                                                            (Pexp_record
                                                               (l, e))))))
                             (Earley.char '}' '}'))))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x) expression))
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _  ->
                               fun e  ->
                                 fun _  ->
                                   match e with
                                   | Some e ->
                                       if Quote.is_antiquotation e.pexp_loc
                                       then e
                                       else loc_expr _loc e.pexp_desc
                                   | None  ->
                                       let cunit = id_loc (Lident "()") _loc
                                          in
                                       loc_expr _loc
                                         (pexp_construct (cunit, None)))
                    (Earley.char ')' ')')))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence no_parser
                 (Earley.fsequence expression
                    (Earley.fsequence type_coercion
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _  ->
                                     fun t  ->
                                       fun e  ->
                                         fun _default_0  ->
                                           fun _  ->
                                             match t with
                                             | (Some t1,None ) ->
                                                 loc_expr (ghost _loc)
                                                   (pexp_constraint (e, t1))
                                             | (t1,Some t2) ->
                                                 loc_expr (ghost _loc)
                                                   (pexp_coerce (e, t1, t2))
                                             | (None ,None ) -> assert false)
                          (Earley.char ')' ')')))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence begin_kw
              (Earley.fsequence
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x) expression))
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _default_0  ->
                               fun e  ->
                                 fun _default_1  ->
                                   match e with
                                   | Some e ->
                                       if Quote.is_antiquotation e.pexp_loc
                                       then e
                                       else loc_expr _loc e.pexp_desc
                                   | None  ->
                                       let cunit = id_loc (Lident "()") _loc
                                          in
                                       loc_expr _loc
                                         (pexp_construct (cunit, None)))
                    end_kw))));
         (((fun lvl  -> lvl <= App)),
           (Earley.fsequence (expression_lvl (NoMatch, (next_exp App)))
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun l  ->
                            fun f  ->
                              loc_expr _loc
                                (match ((f.pexp_desc), l) with
                                 | (Pexp_construct
                                    (c,None ),(Nolabel ,a)::[]) ->
                                     Pexp_construct (c, (Some a))
                                 | (Pexp_variant (c,None ),(Nolabel ,a)::[])
                                     -> Pexp_variant (c, (Some a))
                                 | _ -> Pexp_apply (f, l)))
                 (Earley.apply List.rev
                    (Earley.fixpoint1 []
                       (Earley.apply (fun x  -> fun y  -> x :: y) argument))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence
              (Earley.apply_position
                 (fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  ->
                          fun x  -> ((locate str pos str' pos'), x))
                 constructor)
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun _default_0  ->
                            fun c  ->
                              let (_loc_c,c) = c  in
                              loc_expr _loc
                                (pexp_construct ((id_loc c _loc_c), None)))
                 no_dot)));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun l  -> loc_expr _loc (Pexp_variant (l, None)))
              tag_name));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.string "[|" "[|")
              (Earley.fsequence expression_list
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _  ->
                               fun l  ->
                                 fun _  ->
                                   loc_expr _loc
                                     (Pexp_array (List.map fst l)))
                    (Earley.string "|]" "|]")))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.char '[' '[')
              (Earley.fsequence expression_list
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun cl  ->
                               let (_loc_cl,cl) = cl  in
                               fun l  ->
                                 fun _  ->
                                   loc_expr _loc
                                     (pexp_list _loc ~loc_cl:_loc_cl l).pexp_desc)
                    (Earley.apply_position
                       (fun str  ->
                          fun pos  ->
                            fun str'  ->
                              fun pos'  ->
                                fun x  -> ((locate str pos str' pos'), x))
                       (Earley.char ']' ']'))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.string "{" "{")
              (Earley.fsequence
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x)
                       (Earley.fsequence expression
                          (Earley.apply
                             (fun _  -> fun _default_0  -> _default_0)
                             with_kw))))
                 (Earley.fsequence record_list
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun l  ->
                                    fun e  ->
                                      fun _  ->
                                        loc_expr _loc (Pexp_record (l, e)))
                       (Earley.string "}" "}"))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence while_kw
              (Earley.fsequence expression
                 (Earley.fsequence do_kw
                    (Earley.fsequence expression
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _default_0  ->
                                     fun e'  ->
                                       fun _default_1  ->
                                         fun e  ->
                                           fun _default_2  ->
                                             loc_expr _loc
                                               (Pexp_while (e, e'))) done_kw))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence for_kw
              (Earley.fsequence pattern
                 (Earley.fsequence (Earley.char '=' '=')
                    (Earley.fsequence expression
                       (Earley.fsequence downto_flag
                          (Earley.fsequence expression
                             (Earley.fsequence do_kw
                                (Earley.fsequence expression
                                   (Earley.apply_position
                                      (fun __loc__start__buf  ->
                                         fun __loc__start__pos  ->
                                           fun __loc__end__buf  ->
                                             fun __loc__end__pos  ->
                                               let _loc =
                                                 locate __loc__start__buf
                                                   __loc__start__pos
                                                   __loc__end__buf
                                                   __loc__end__pos
                                                  in
                                               fun _default_0  ->
                                                 fun e''  ->
                                                   fun _default_1  ->
                                                     fun e'  ->
                                                       fun d  ->
                                                         fun e  ->
                                                           fun _  ->
                                                             fun id  ->
                                                               fun _default_2
                                                                  ->
                                                                 loc_expr
                                                                   _loc
                                                                   (Pexp_for
                                                                    (id, e,
                                                                    e', d,
                                                                    e'')))
                                      done_kw))))))))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence new_kw
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun p  ->
                            let (_loc_p,p) = p  in
                            fun _default_0  ->
                              loc_expr _loc (Pexp_new (id_loc p _loc_p)))
                 (Earley.apply_position
                    (fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  ->
                             fun x  -> ((locate str pos str' pos'), x))
                    class_path))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence object_kw
              (Earley.fsequence class_body
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _default_0  ->
                               fun o  ->
                                 fun _default_1  ->
                                   loc_expr _loc (Pexp_object o)) end_kw))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.string "{<" "{<")
              (Earley.fsequence
                 (Earley.option []
                    (Earley.fsequence obj_item
                       (Earley.fsequence
                          (Earley.apply List.rev
                             (Earley.fixpoint []
                                (Earley.apply (fun x  -> fun y  -> x :: y)
                                   (Earley.fsequence semi_col
                                      (Earley.apply (fun o  -> fun _  -> o)
                                         obj_item)))))
                          (Earley.apply
                             (fun _  -> fun l  -> fun o  -> o :: l)
                             (Earley.option None
                                (Earley.apply (fun x  -> Some x) semi_col))))))
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun _  ->
                               fun l  ->
                                 fun _  -> loc_expr _loc (Pexp_override l))
                    (Earley.string ">}" ">}")))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence module_kw
                 (Earley.fsequence module_expr
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x)
                             (Earley.fsequence (Earley.string ":" ":")
                                (Earley.apply (fun pt  -> fun _  -> pt)
                                   package_type))))
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _  ->
                                     fun pt  ->
                                       fun me  ->
                                         fun _default_0  ->
                                           fun _  ->
                                             let desc =
                                               match pt with
                                               | None  -> Pexp_pack me
                                               | Some pt ->
                                                   let me =
                                                     loc_expr (ghost _loc)
                                                       (Pexp_pack me)
                                                      in
                                                   let pt =
                                                     loc_typ (ghost _loc)
                                                       pt.ptyp_desc
                                                      in
                                                   pexp_constraint (me, pt)
                                                in
                                             loc_expr _loc desc)
                          (Earley.char ')' ')')))))));
         (((fun lvl  -> lvl <= Dot)),
           (Earley.fsequence (expression_lvl (NoMatch, Dot))
              (Earley.fsequence (Earley.char '.' '.')
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun r  -> fun _  -> fun e'  -> r e' _loc)
                    (Earley.alternatives
                       [Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun f  ->
                                     let (_loc_f,f) = f  in
                                     fun e'  ->
                                       fun _loc  ->
                                         let f = id_loc f _loc_f  in
                                         loc_expr _loc (Pexp_field (e', f)))
                          (Earley.apply_position
                             (fun str  ->
                                fun pos  ->
                                  fun str'  ->
                                    fun pos'  ->
                                      fun x  ->
                                        ((locate str pos str' pos'), x))
                             field);
                       Earley.fsequence (Earley.string "(" "(")
                         (Earley.fsequence expression
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun f  ->
                                            fun _  ->
                                              fun e'  ->
                                                fun _loc  ->
                                                  exp_apply _loc
                                                    (array_function
                                                       (ghost
                                                          (merge2 e'.pexp_loc
                                                             _loc)) "Array"
                                                       "get") [e'; f])
                               (Earley.string ")" ")")));
                       Earley.fsequence (Earley.string "[" "[")
                         (Earley.fsequence expression
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun f  ->
                                            fun _  ->
                                              fun e'  ->
                                                fun _loc  ->
                                                  exp_apply _loc
                                                    (array_function
                                                       (ghost
                                                          (merge2 e'.pexp_loc
                                                             _loc)) "String"
                                                       "get") [e'; f])
                               (Earley.string "]" "]")));
                       Earley.fsequence (Earley.string "{" "{")
                         (Earley.fsequence expression
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun f  ->
                                            fun _  ->
                                              fun e'  ->
                                                fun _loc  ->
                                                  bigarray_get
                                                    (ghost
                                                       (merge2 e'.pexp_loc
                                                          _loc)) e' f)
                               (Earley.string "}" "}")))])))));
         (((fun lvl  -> lvl <= Dash)),
           (Earley.fsequence (expression_lvl (NoMatch, Dash))
              (Earley.fsequence (Earley.char '#' '#')
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun f  ->
                               fun _  -> fun e'  -> Exp.send ~loc:_loc e' f)
                    method_name))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.char '$' '$')
              (Earley.fsequence (Earley.no_blank_test ())
                 (Earley.apply_position
                    (fun __loc__start__buf  ->
                       fun __loc__start__pos  ->
                         fun __loc__end__buf  ->
                           fun __loc__end__pos  ->
                             let _loc =
                               locate __loc__start__buf __loc__start__pos
                                 __loc__end__buf __loc__end__pos
                                in
                             fun c  ->
                               fun _  ->
                                 fun _  ->
                                   match c with
                                   | "FILE" ->
                                       exp_string _loc
                                         (start_pos _loc).Lexing.pos_fname
                                   | "LINE" ->
                                       exp_int _loc
                                         (start_pos _loc).Lexing.pos_lnum
                                   | _ ->
                                       (try
                                          let str = Sys.getenv c  in
                                          parse_string ~filename:("ENV:" ^ c)
                                            expression ocaml_blank str
                                        with | Not_found  -> give_up ()))
                    uident))));
         (((fun lvl  -> lvl <= Atom)),
           (Earley.fsequence (Earley.string "<:" "<:")
              (Earley.apply (fun r  -> fun _  -> r)
                 (Earley.alternatives
                    [Earley.fsequence (Earley.string "record" "record")
                       (Earley.fsequence (Earley.char '<' '<')
                          (Earley.fsequence
                             (Earley.apply_position
                                (fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         fun x  ->
                                           ((locate str pos str' pos'), x))
                                record_list)
                             (Earley.apply_position
                                (fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos
                                            in
                                         fun _  ->
                                           fun e  ->
                                             let (_loc_e,e) = e  in
                                             fun _  ->
                                               fun _  ->
                                                 let e_loc =
                                                   exp_ident _loc "_loc"  in
                                                 let quote_fields =
                                                   let open Quote in
                                                     quote_list
                                                       (fun e_loc  ->
                                                          fun _loc  ->
                                                            fun (x1,x2)  ->
                                                              quote_tuple
                                                                e_loc _loc
                                                                [(quote_loc
                                                                    quote_longident)
                                                                   e_loc _loc
                                                                   x1;
                                                                quote_expression
                                                                  e_loc _loc
                                                                  x2])
                                                    in
                                                 quote_fields e_loc _loc_e e)
                                (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "expr" "expr")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               expression)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                Quote.quote_expression e_loc
                                                  _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "type" "type")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               typexpr)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                Quote.quote_core_type e_loc
                                                  _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "pat" "pat")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               pattern)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                Quote.quote_pattern e_loc
                                                  _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "struct" "struct")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               structure_item_simple)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                Quote.quote_structure e_loc
                                                  _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "sig" "sig")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               signature_item)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                Quote.quote_signature e_loc
                                                  _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence
                      (Earley.string "constructors" "constructors")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               constr_decl_list)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                let open Quote in
                                                  quote_list
                                                    quote_constructor_declaration
                                                    e_loc _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "fields" "fields")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               field_decl_list)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                let open Quote in
                                                  quote_list
                                                    quote_label_declaration
                                                    e_loc _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "bindings" "bindings")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               let_binding)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                let open Quote in
                                                  quote_list
                                                    quote_value_binding e_loc
                                                    _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "cases" "cases")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               match_cases)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                let open Quote in
                                                  quote_list quote_case e_loc
                                                    _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "module" "module")
                      (Earley.fsequence (Earley.char '<' '<')
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               module_expr)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun _  ->
                                          fun e  ->
                                            let (_loc_e,e) = e  in
                                            fun _  ->
                                              fun _  ->
                                                let e_loc =
                                                  exp_ident _loc "_loc"  in
                                                Quote.quote_module_expr e_loc
                                                  _loc_e e)
                               (Earley.string ">>" ">>"))));
                    Earley.fsequence (Earley.string "module" "module")
                      (Earley.fsequence (Earley.string "type" "type")
                         (Earley.fsequence (Earley.char '<' '<')
                            (Earley.fsequence
                               (Earley.apply_position
                                  (fun str  ->
                                     fun pos  ->
                                       fun str'  ->
                                         fun pos'  ->
                                           fun x  ->
                                             ((locate str pos str' pos'), x))
                                  module_type)
                               (Earley.apply_position
                                  (fun __loc__start__buf  ->
                                     fun __loc__start__pos  ->
                                       fun __loc__end__buf  ->
                                         fun __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos
                                              in
                                           fun _  ->
                                             fun e  ->
                                               let (_loc_e,e) = e  in
                                               fun _  ->
                                                 fun _  ->
                                                   fun _  ->
                                                     let e_loc =
                                                       exp_ident _loc "_loc"
                                                        in
                                                     Quote.quote_module_type
                                                       e_loc _loc_e e)
                                  (Earley.string ">>" ">>")))))]))))],
          (fun lvl  -> []))
      
    let (semicol,semicol__set__grammar) = Earley.grammar_prio "semicol" 
    let _ =
      semicol__set__grammar
        ([(((fun (alm,lvl)  -> lvl > Seq)),
            (Earley.apply (fun _  -> false) (Earley.empty ())));
         (((fun (alm,lvl)  -> lvl = Seq)),
           (Earley.apply (fun _default_0  -> true) semi_col));
         (((fun (alm,lvl)  -> lvl = Seq)),
           (Earley.apply (fun _default_0  -> false) no_semi))],
          (fun (alm,lvl)  -> []))
      
    let (noelse,noelse__set__grammar) = Earley.grammar_prio "noelse" 
    let _ =
      noelse__set__grammar
        ([(((fun b  -> not b)),
            (Earley.apply (fun _  -> ()) (Earley.empty ())));
         (((fun b  -> b)), no_else)], (fun b  -> []))
      
    let (debut,debut__set__grammar) = Earley.grammar_family "debut" 
    let debut __curry__varx0 __curry__varx1 =
      debut (__curry__varx0, __curry__varx1) 
    let _ =
      debut__set__grammar
        (fun (lvl,alm)  ->
           Earley.apply
             (fun ((_,(lvl0,no_else,f)) as s)  ->
                let (_loc_s,s) = s  in ((lvl0, no_else), (f, _loc_s)))
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                (left_expr (alm, lvl))))
      
    let (suit,suit__set__grammar) = Earley.grammar_family "suit" 
    let suit __curry__varx0 __curry__varx1 __curry__varx2 =
      suit (__curry__varx0, __curry__varx1, __curry__varx2) 
    let _ =
      suit__set__grammar
        (fun (lvl,alm,(lvl0,no_else))  ->
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                (expression_lvl (alm, lvl0)))
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   (semicol (alm, lvl)))
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun _default_0  ->
                              fun c  ->
                                let (_loc_c,c) = c  in
                                fun e  ->
                                  let (_loc_e,e) = e  in
                                  fun (f,_loc_s)  ->
                                    let _loc = merge2 _loc_s _loc_e  in
                                    let _loc_c = if c then _loc_c else _loc_e
                                       in
                                    f e (_loc, _loc_c)) (noelse no_else))))
      
    let _ =
      set_expression_lvl
        (fun ((alm,lvl) as c)  ->
           Earley.alternatives
             ((if allow_match alm
               then
                 [Earley.fsequence prefix_expression
                    (Earley.apply (fun _default_0  -> fun r  -> r)
                       (semicol (alm, lvl)))]
               else []) @
                [Earley.fsequence (extra_expressions_grammar c)
                   (Earley.apply (fun _default_0  -> fun e  -> e)
                      (semicol (alm, lvl)));
                Earley.dependent_sequence (debut lvl alm) (suit lvl alm);
                Earley.fsequence (right_expression lvl)
                  (Earley.apply (fun _default_0  -> fun r  -> r)
                     (semicol (alm, lvl)))]))
      
    let module_expr_base = Earley.declare_grammar "module_expr_base" 
    let _ =
      Earley.set_grammar module_expr_base
        (Earley.alternatives
           [Earley.fsequence (Earley.char '(' '(')
              (Earley.fsequence val_kw
                 (Earley.fsequence expression
                    (Earley.fsequence
                       (Earley.option None
                          (Earley.apply (fun x  -> Some x)
                             (Earley.fsequence (Earley.string ":" ":")
                                (Earley.apply (fun pt  -> fun _  -> pt)
                                   package_type))))
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _  ->
                                     fun pt  ->
                                       fun e  ->
                                         fun _default_0  ->
                                           fun _  ->
                                             let e =
                                               match pt with
                                               | None  -> Pmod_unpack e
                                               | Some pt ->
                                                   Pmod_unpack
                                                     (loc_expr (ghost _loc)
                                                        (pexp_constraint
                                                           (e, pt)))
                                                in
                                             mexpr_loc _loc e)
                          (Earley.char ')' ')')))));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun mp  ->
                        let mid = id_loc mp _loc  in
                        mexpr_loc _loc (Pmod_ident mid)) module_path;
           Earley.fsequence
             (Earley.apply (fun _default_0  -> push_comments ()) struct_kw)
             (Earley.fsequence
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun ms  -> ms @ (attach_str _loc)) structure)
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun _default_0  ->
                              fun ms  ->
                                fun _default_1  ->
                                  mexpr_loc _loc (Pmod_structure ms))
                   (Earley.apply (fun _default_0  -> pop_comments ()) end_kw)));
           Earley.fsequence functor_kw
             (Earley.fsequence (Earley.char '(' '(')
                (Earley.fsequence module_name
                   (Earley.fsequence
                      (Earley.option None
                         (Earley.apply (fun x  -> Some x)
                            (Earley.fsequence (Earley.char ':' ':')
                               (Earley.apply (fun mt  -> fun _  -> mt)
                                  module_type))))
                      (Earley.fsequence (Earley.char ')' ')')
                         (Earley.fsequence arrow_re
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun me  ->
                                          fun _default_0  ->
                                            fun _  ->
                                              fun mt  ->
                                                fun mn  ->
                                                  fun _  ->
                                                    fun _default_1  ->
                                                      mexpr_loc _loc
                                                        (Pmod_functor
                                                           (mn, mt, me)))
                               module_expr))))));
           Earley.fsequence (Earley.char '(' '(')
             (Earley.fsequence module_expr
                (Earley.fsequence
                   (Earley.option None
                      (Earley.apply (fun x  -> Some x)
                         (Earley.fsequence (Earley.char ':' ':')
                            (Earley.apply (fun mt  -> fun _  -> mt)
                               module_type))))
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun _  ->
                                 fun mt  ->
                                   fun me  ->
                                     fun _  ->
                                       match mt with
                                       | None  -> me
                                       | Some mt ->
                                           mexpr_loc _loc
                                             (Pmod_constraint (me, mt)))
                      (Earley.char ')' ')'))))])
      
    let _ =
      set_grammar module_expr
        (Earley.fsequence
           (Earley.apply_position
              (fun str  ->
                 fun pos  ->
                   fun str'  ->
                     fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
              module_expr_base)
           (Earley.apply
              (fun l  ->
                 fun m  ->
                   let (_loc_m,m) = m  in
                   List.fold_left
                     (fun acc  ->
                        fun (_loc_n,n)  ->
                          mexpr_loc (merge2 _loc_m _loc_n)
                            (Pmod_apply (acc, n))) m l)
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.fsequence (Earley.string "(" "(")
                          (Earley.fsequence module_expr
                             (Earley.apply_position
                                (fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos
                                            in
                                         fun _  ->
                                           fun m  -> fun _  -> (_loc, m))
                                (Earley.string ")" ")")))))))))
      
    let module_type_base = Earley.declare_grammar "module_type_base" 
    let _ =
      Earley.set_grammar module_type_base
        (Earley.alternatives
           [Earley.fsequence module_kw
              (Earley.fsequence type_kw
                 (Earley.fsequence of_kw
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun me  ->
                                  fun _default_0  ->
                                    fun _default_1  ->
                                      fun _default_2  ->
                                        mtyp_loc _loc (Pmty_typeof me))
                       module_expr)));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun mp  ->
                        let mid = id_loc mp _loc  in
                        mtyp_loc _loc (Pmty_ident mid)) modtype_path;
           Earley.fsequence
             (Earley.apply (fun _default_0  -> push_comments ()) sig_kw)
             (Earley.fsequence
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun ms  -> ms @ (attach_sig _loc)) signature)
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun _default_0  ->
                              fun ms  ->
                                fun _default_1  ->
                                  mtyp_loc _loc (Pmty_signature ms))
                   (Earley.apply (fun _default_0  -> pop_comments ()) end_kw)));
           Earley.fsequence functor_kw
             (Earley.fsequence (Earley.char '(' '(')
                (Earley.fsequence module_name
                   (Earley.fsequence
                      (Earley.option None
                         (Earley.apply (fun x  -> Some x)
                            (Earley.fsequence (Earley.char ':' ':')
                               (Earley.apply (fun mt  -> fun _  -> mt)
                                  module_type))))
                      (Earley.fsequence (Earley.char ')' ')')
                         (Earley.fsequence arrow_re
                            (Earley.fsequence module_type
                               (Earley.apply_position
                                  (fun __loc__start__buf  ->
                                     fun __loc__start__pos  ->
                                       fun __loc__end__buf  ->
                                         fun __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos
                                              in
                                           fun _default_0  ->
                                             fun me  ->
                                               fun _default_1  ->
                                                 fun _  ->
                                                   fun mt  ->
                                                     fun mn  ->
                                                       fun _  ->
                                                         fun _default_2  ->
                                                           mtyp_loc _loc
                                                             (Pmty_functor
                                                                (mn, mt, me)))
                                  no_with)))))));
           Earley.fsequence (Earley.string "(" "(")
             (Earley.fsequence module_type
                (Earley.apply (fun _  -> fun mt  -> fun _  -> mt)
                   (Earley.string ")" ")")))])
      
    let mod_constraint = Earley.declare_grammar "mod_constraint" 
    let _ =
      Earley.set_grammar mod_constraint
        (Earley.alternatives
           [Earley.fsequence module_kw
              (Earley.fsequence module_name
                 (Earley.fsequence (Earley.string ":=" ":=")
                    (Earley.apply
                       (fun emp  ->
                          let (_loc_emp,emp) = emp  in
                          fun _  ->
                            fun mn  ->
                              fun _default_0  ->
                                Pwith_modsubst (mn, (id_loc emp _loc_emp)))
                       (Earley.apply_position
                          (fun str  ->
                             fun pos  ->
                               fun str'  ->
                                 fun pos'  ->
                                   fun x  -> ((locate str pos str' pos'), x))
                          extended_module_path))));
           Earley.fsequence
             (Earley.apply_position
                (fun str  ->
                   fun pos  ->
                     fun str'  ->
                       fun pos'  -> fun x  -> ((locate str pos str' pos'), x))
                type_kw)
             (Earley.apply
                (fun tf  ->
                   fun t  ->
                     let (_loc_t,t) = t  in
                     let (tn,ty) = tf (Some _loc_t)  in Pwith_type (tn, ty))
                typedef_in_constraint);
           Earley.fsequence module_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   module_path)
                (Earley.fsequence (Earley.char '=' '=')
                   (Earley.apply
                      (fun m2  ->
                         let (_loc_m2,m2) = m2  in
                         fun _  ->
                           fun m1  ->
                             let (_loc_m1,m1) = m1  in
                             fun _default_0  ->
                               let name = id_loc m1 _loc_m1  in
                               Pwith_module (name, (id_loc m2 _loc_m2)))
                      (Earley.apply_position
                         (fun str  ->
                            fun pos  ->
                              fun str'  ->
                                fun pos'  ->
                                  fun x  -> ((locate str pos str' pos'), x))
                         extended_module_path))));
           Earley.fsequence type_kw
             (Earley.fsequence type_params
                (Earley.fsequence
                   (Earley.apply_position
                      (fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  ->
                               fun x  -> ((locate str pos str' pos'), x))
                      typeconstr)
                   (Earley.fsequence (Earley.string ":=" ":=")
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun te  ->
                                    fun _  ->
                                      fun tcn  ->
                                        let (_loc_tcn,tcn) = tcn  in
                                        fun tps  ->
                                          fun _default_0  ->
                                            let tcn0 =
                                              id_loc (Longident.last tcn)
                                                _loc_tcn
                                               in
                                            let _tcn = id_loc tcn _loc_tcn
                                               in
                                            let td =
                                              type_declaration _loc tcn0 tps
                                                [] Ptype_abstract Public
                                                (Some te)
                                               in
                                            Pwith_typesubst td) typexpr))))])
      
    let _ =
      set_grammar module_type
        (Earley.fsequence module_type_base
           (Earley.apply_position
              (fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       fun l  ->
                         fun m  ->
                           match l with
                           | None  -> m
                           | Some l -> mtyp_loc _loc (Pmty_with (m, l)))
              (Earley.option None
                 (Earley.apply (fun x  -> Some x)
                    (Earley.fsequence with_kw
                       (Earley.fsequence mod_constraint
                          (Earley.apply
                             (fun l  -> fun m  -> fun _  -> m :: l)
                             (Earley.apply List.rev
                                (Earley.fixpoint []
                                   (Earley.apply (fun x  -> fun y  -> x :: y)
                                      (Earley.fsequence and_kw
                                         (Earley.apply
                                            (fun _default_0  ->
                                               fun _  -> _default_0)
                                            mod_constraint))))))))))))
      
    let structure_item_base = Earley.declare_grammar "structure_item_base" 
    let _ =
      Earley.set_grammar structure_item_base
        (Earley.alternatives
           [Earley.fsequence (Earley.string "$struct:" "$struct:")
              (Earley.fsequence expression
                 (Earley.fsequence (Earley.no_blank_test ())
                    (Earley.apply_position
                       (fun __loc__start__buf  ->
                          fun __loc__start__pos  ->
                            fun __loc__end__buf  ->
                              fun __loc__end__pos  ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos
                                   in
                                fun _  ->
                                  fun _  ->
                                    fun e  ->
                                      fun _  ->
                                        let open Quote in
                                          pstr_antiquotation _loc
                                            (function
                                             | Quote_pstr  ->
                                                 let e_loc =
                                                   exp_ident _loc "_loc"  in
                                                 quote_apply e_loc _loc
                                                   (pa_ast "loc_str")
                                                   [quote_location_t e_loc
                                                      _loc _loc;
                                                   quote_const e_loc _loc
                                                     (parsetree
                                                        "Pstr_include")
                                                     [quote_record e_loc _loc
                                                        [((parsetree
                                                             "pincl_loc"),
                                                           (quote_location_t
                                                              e_loc _loc _loc));
                                                        ((parsetree
                                                            "pincl_attributes"),
                                                          (quote_list
                                                             quote_attribute
                                                             e_loc _loc []));
                                                        ((parsetree
                                                            "pincl_mod"),
                                                          (quote_apply e_loc
                                                             _loc
                                                             (pa_ast
                                                                "mexpr_loc")
                                                             [quote_location_t
                                                                e_loc _loc
                                                                _loc;
                                                             quote_const
                                                               e_loc _loc
                                                               (parsetree
                                                                  "Pmod_structure")
                                                               [e]]))]]]
                                             | _ ->
                                                 failwith
                                                   "Bad antiquotation..."))
                       (Earley.char '$' '$'))));
           Earley.fsequence
             (EarleyStr.regexp ~name:"let" let_re (fun groupe  -> groupe 0))
             (Earley.fsequence rec_flag
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun l  ->
                              fun r  ->
                                fun _default_0  ->
                                  loc_str _loc
                                    (match l with | _ -> Pstr_value (r, l)))
                   let_binding));
           Earley.fsequence external_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   value_name)
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.fsequence typexpr
                      (Earley.fsequence (Earley.string "=" "=")
                         (Earley.fsequence
                            (Earley.apply List.rev
                               (Earley.fixpoint []
                                  (Earley.apply (fun x  -> fun y  -> x :: y)
                                     string_litteral)))
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun a  ->
                                          fun ls  ->
                                            fun _  ->
                                              fun ty  ->
                                                fun _  ->
                                                  fun n  ->
                                                    let (_loc_n,n) = n  in
                                                    fun _default_0  ->
                                                      let ls =
                                                        List.map fst ls  in
                                                      let l = List.length ls
                                                         in
                                                      if (l < 1) || (l > 3)
                                                      then give_up ();
                                                      loc_str _loc
                                                        (Pstr_primitive
                                                           {
                                                             pval_name =
                                                               (id_loc n
                                                                  _loc_n);
                                                             pval_type = ty;
                                                             pval_prim = ls;
                                                             pval_loc = _loc;
                                                             pval_attributes
                                                               =
                                                               (attach_attrib
                                                                  _loc a)
                                                           }))
                               post_item_attributes))))));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun td  -> Str.type_ ~loc:_loc Recursive td)
             type_definition;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun te  -> Str.type_extension ~loc:_loc te)
             type_extension;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ex  -> loc_str _loc ex) exception_definition;
           Earley.fsequence module_kw
             (Earley.apply_position
                (fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos
                            in
                         fun r  -> fun _default_0  -> loc_str _loc r)
                (Earley.alternatives
                   [Earley.fsequence type_kw
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     fun x  ->
                                       ((locate str pos str' pos'), x))
                            modtype_name)
                         (Earley.fsequence
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.fsequence (Earley.string "=" "=")
                                     (Earley.apply (fun mt  -> fun _  -> mt)
                                        module_type))))
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun a  ->
                                          fun mt  ->
                                            fun mn  ->
                                              let (_loc_mn,mn) = mn  in
                                              fun _default_0  ->
                                                Pstr_modtype
                                                  {
                                                    pmtd_name =
                                                      (id_loc mn _loc_mn);
                                                    pmtd_type = mt;
                                                    pmtd_attributes =
                                                      (attach_attrib _loc a);
                                                    pmtd_loc = _loc
                                                  }) post_item_attributes)));
                   Earley.fsequence rec_kw
                     (Earley.fsequence module_name
                        (Earley.fsequence
                           (Earley.apply_position
                              (fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       fun x  ->
                                         ((locate str pos str' pos'), x))
                              (Earley.option None
                                 (Earley.apply (fun x  -> Some x)
                                    (Earley.fsequence (Earley.string ":" ":")
                                       (Earley.apply
                                          (fun mt  -> fun _  -> mt)
                                          module_type)))))
                           (Earley.fsequence (Earley.char '=' '=')
                              (Earley.fsequence
                                 (Earley.apply_position
                                    (fun str  ->
                                       fun pos  ->
                                         fun str'  ->
                                           fun pos'  ->
                                             fun x  ->
                                               ((locate str pos str' pos'),
                                                 x)) module_expr)
                                 (Earley.apply
                                    (fun ms  ->
                                       fun me  ->
                                         let (_loc_me,me) = me  in
                                         fun _  ->
                                           fun mt  ->
                                             let (_loc_mt,mt) = mt  in
                                             fun mn  ->
                                               fun _default_0  ->
                                                 let m =
                                                   module_binding
                                                     (merge2 _loc_mt _loc_me)
                                                     mn mt me
                                                    in
                                                 Pstr_recmodule (m :: ms))
                                    (Earley.apply List.rev
                                       (Earley.fixpoint []
                                          (Earley.apply
                                             (fun x  -> fun y  -> x :: y)
                                             (Earley.fsequence and_kw
                                                (Earley.fsequence module_name
                                                   (Earley.fsequence
                                                      (Earley.apply_position
                                                         (fun str  ->
                                                            fun pos  ->
                                                              fun str'  ->
                                                                fun pos'  ->
                                                                  fun x  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                         (Earley.option None
                                                            (Earley.apply
                                                               (fun x  ->
                                                                  Some x)
                                                               (Earley.fsequence
                                                                  (Earley.string
                                                                    ":" ":")
                                                                  (Earley.apply
                                                                    (fun mt 
                                                                    ->
                                                                    fun _  ->
                                                                    mt)
                                                                    module_type)))))
                                                      (Earley.fsequence
                                                         (Earley.char '=' '=')
                                                         (Earley.apply
                                                            (fun me  ->
                                                               let (_loc_me,me)
                                                                 = me  in
                                                               fun _  ->
                                                                 fun mt  ->
                                                                   let 
                                                                    (_loc_mt,mt)
                                                                    = mt  in
                                                                   fun mn  ->
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    module_binding
                                                                    (merge2
                                                                    _loc_mt
                                                                    _loc_me)
                                                                    mn mt me)
                                                            (Earley.apply_position
                                                               (fun str  ->
                                                                  fun pos  ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    fun x  ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                               module_expr))))))))))))));
                   Earley.fsequence module_name
                     (Earley.fsequence
                        (Earley.apply List.rev
                           (Earley.fixpoint []
                              (Earley.apply (fun x  -> fun y  -> x :: y)
                                 (Earley.fsequence (Earley.string "(" "(")
                                    (Earley.fsequence module_name
                                       (Earley.fsequence
                                          (Earley.option None
                                             (Earley.apply (fun x  -> Some x)
                                                (Earley.fsequence
                                                   (Earley.string ":" ":")
                                                   (Earley.apply
                                                      (fun mt  ->
                                                         fun _  -> mt)
                                                      module_type))))
                                          (Earley.apply_position
                                             (fun __loc__start__buf  ->
                                                fun __loc__start__pos  ->
                                                  fun __loc__end__buf  ->
                                                    fun __loc__end__pos  ->
                                                      let _loc =
                                                        locate
                                                          __loc__start__buf
                                                          __loc__start__pos
                                                          __loc__end__buf
                                                          __loc__end__pos
                                                         in
                                                      fun _  ->
                                                        fun mt  ->
                                                          fun mn  ->
                                                            fun _  ->
                                                              (mn, mt, _loc))
                                             (Earley.string ")" ")"))))))))
                        (Earley.fsequence
                           (Earley.apply_position
                              (fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       fun x  ->
                                         ((locate str pos str' pos'), x))
                              (Earley.option None
                                 (Earley.apply (fun x  -> Some x)
                                    (Earley.fsequence (Earley.string ":" ":")
                                       (Earley.apply
                                          (fun mt  -> fun _  -> mt)
                                          module_type)))))
                           (Earley.fsequence (Earley.string "=" "=")
                              (Earley.apply_position
                                 (fun __loc__start__buf  ->
                                    fun __loc__start__pos  ->
                                      fun __loc__end__buf  ->
                                        fun __loc__end__pos  ->
                                          let _loc =
                                            locate __loc__start__buf
                                              __loc__start__pos
                                              __loc__end__buf __loc__end__pos
                                             in
                                          fun me  ->
                                            let (_loc_me,me) = me  in
                                            fun _  ->
                                              fun mt  ->
                                                let (_loc_mt,mt) = mt  in
                                                fun l  ->
                                                  fun mn  ->
                                                    let me =
                                                      match mt with
                                                      | None  -> me
                                                      | Some mt ->
                                                          mexpr_loc
                                                            (merge2 _loc_mt
                                                               _loc_me)
                                                            (Pmod_constraint
                                                               (me, mt))
                                                       in
                                                    let me =
                                                      List.fold_left
                                                        (fun acc  ->
                                                           fun (mn,mt,_loc) 
                                                             ->
                                                             mexpr_loc
                                                               (merge2 _loc
                                                                  _loc_me)
                                                               (Pmod_functor
                                                                  (mn, mt,
                                                                    acc))) me
                                                        (List.rev l)
                                                       in
                                                    Pstr_module
                                                      (module_binding _loc mn
                                                         None me))
                                 (Earley.apply_position
                                    (fun str  ->
                                       fun pos  ->
                                         fun str'  ->
                                           fun pos'  ->
                                             fun x  ->
                                               ((locate str pos str' pos'),
                                                 x)) module_expr)))))]));
           Earley.fsequence open_kw
             (Earley.fsequence override_flag
                (Earley.fsequence
                   (Earley.apply_position
                      (fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  ->
                               fun x  -> ((locate str pos str' pos'), x))
                      module_path)
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun a  ->
                                 fun m  ->
                                   let (_loc_m,m) = m  in
                                   fun o  ->
                                     fun _default_0  ->
                                       loc_str _loc
                                         (Pstr_open
                                            {
                                              popen_lid = (id_loc m _loc_m);
                                              popen_override = o;
                                              popen_loc = _loc;
                                              popen_attributes =
                                                (attach_attrib _loc a)
                                            })) post_item_attributes)));
           Earley.fsequence include_kw
             (Earley.fsequence module_expr
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun a  ->
                              fun me  ->
                                fun _default_0  ->
                                  loc_str _loc
                                    (Pstr_include
                                       {
                                         pincl_mod = me;
                                         pincl_loc = _loc;
                                         pincl_attributes =
                                           (attach_attrib _loc a)
                                       })) post_item_attributes));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ctd  -> loc_str _loc (Pstr_class_type ctd))
             classtype_definition;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun cds  -> loc_str _loc (Pstr_class cds))
             class_definition;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ((s,l) as _default_0)  ->
                        loc_str _loc (Pstr_attribute (s, l)))
             floating_attribute;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ((s,l) as _default_0)  ->
                        loc_str _loc (Pstr_extension ((s, l), [])))
             floating_extension])
      
    let structure_item_aux = Earley.declare_grammar "structure_item_aux" 
    let _ =
      Earley.set_grammar structure_item_aux
        (Earley.alternatives
           [Earley.fsequence structure_item_aux
              (Earley.fsequence double_semi_col
                 (Earley.fsequence ext_attributes
                    (Earley.apply
                       (fun e  ->
                          let (_loc_e,e) = e  in
                          fun _  ->
                            fun _default_0  ->
                              fun s1  -> (loc_str _loc_e (pstr_eval e)) ::
                                (List.rev_append (attach_str _loc_e) s1))
                       (Earley.apply_position
                          (fun str  ->
                             fun pos  ->
                               fun str'  ->
                                 fun pos'  ->
                                   fun x  -> ((locate str pos str' pos'), x))
                          expression))));
           Earley.apply (fun _  -> []) ext_attributes;
           Earley.fsequence ext_attributes
             (Earley.apply_position
                (fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos
                            in
                         fun e  ->
                           let (_loc_e,e) = e  in
                           fun _  ->
                             (attach_str _loc) @
                               [loc_str _loc_e (pstr_eval e)])
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   expression));
           Earley.fsequence structure_item_aux
             (Earley.fsequence (Earley.option () double_semi_col)
                (Earley.fsequence ext_attributes
                   (Earley.apply
                      (fun f  -> fun _  -> fun _default_0  -> fun s1  -> f s1)
                      (Earley.alternatives
                         [Earley.apply
                            (fun s2  ->
                               let (_loc_s2,s2) = s2  in
                               fun s1  -> s2 ::
                                 (List.rev_append (attach_str _loc_s2) s1))
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               structure_item_base);
                         Earley.apply
                           (fun e  ->
                              let (_loc_e,e) = e  in
                              fun s1  ->
                                List.rev_append e
                                  (List.rev_append (attach_str _loc_e) s1))
                           (Earley.apply_position
                              (fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       fun x  ->
                                         ((locate str pos str' pos'), x))
                              (alternatives extra_structure))]))))])
      
    let _ =
      set_grammar structure_item
        (Earley.fsequence structure_item_aux
           (Earley.apply (fun _default_0  -> fun l  -> List.rev l)
              (Earley.option () double_semi_col)))
      
    let _ =
      set_grammar structure_item_simple
        (Earley.apply List.rev
           (Earley.fixpoint []
              (Earley.apply (fun x  -> fun y  -> x :: y) structure_item_base)))
      
    let signature_item_base = Earley.declare_grammar "signature_item_base" 
    let _ =
      Earley.set_grammar signature_item_base
        (Earley.alternatives
           [Earley.fsequence (Earley.char '$' '$')
              (Earley.fsequence (Earley.no_blank_test ())
                 (Earley.fsequence expression
                    (Earley.fsequence (Earley.no_blank_test ())
                       (Earley.apply_position
                          (fun __loc__start__buf  ->
                             fun __loc__start__pos  ->
                               fun __loc__end__buf  ->
                                 fun __loc__end__pos  ->
                                   let _loc =
                                     locate __loc__start__buf
                                       __loc__start__pos __loc__end__buf
                                       __loc__end__pos
                                      in
                                   fun _  ->
                                     fun _  ->
                                       fun e  ->
                                         fun _  ->
                                           fun dol  ->
                                             let open Quote in
                                               psig_antiquotation _loc
                                                 (function
                                                  | Quote_psig  -> e
                                                  | _ ->
                                                      failwith
                                                        "Bad antiquotation..."))
                          (Earley.char '$' '$')))));
           Earley.fsequence val_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   value_name)
                (Earley.fsequence (Earley.char ':' ':')
                   (Earley.fsequence typexpr
                      (Earley.apply_position
                         (fun __loc__start__buf  ->
                            fun __loc__start__pos  ->
                              fun __loc__end__buf  ->
                                fun __loc__end__pos  ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos
                                     in
                                  fun a  ->
                                    fun ty  ->
                                      fun _  ->
                                        fun n  ->
                                          let (_loc_n,n) = n  in
                                          fun _default_0  ->
                                            loc_sig _loc
                                              (psig_value
                                                 ~attributes:(attach_attrib
                                                                _loc a) _loc
                                                 (id_loc n _loc_n) ty []))
                         post_item_attributes))));
           Earley.fsequence external_kw
             (Earley.fsequence
                (Earley.apply_position
                   (fun str  ->
                      fun pos  ->
                        fun str'  ->
                          fun pos'  ->
                            fun x  -> ((locate str pos str' pos'), x))
                   value_name)
                (Earley.fsequence (Earley.string ":" ":")
                   (Earley.fsequence typexpr
                      (Earley.fsequence (Earley.string "=" "=")
                         (Earley.fsequence
                            (Earley.apply List.rev
                               (Earley.fixpoint []
                                  (Earley.apply (fun x  -> fun y  -> x :: y)
                                     string_litteral)))
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun a  ->
                                          fun ls  ->
                                            fun _  ->
                                              fun ty  ->
                                                fun _  ->
                                                  fun n  ->
                                                    let (_loc_n,n) = n  in
                                                    fun _default_0  ->
                                                      let ls =
                                                        List.map fst ls  in
                                                      let l = List.length ls
                                                         in
                                                      if (l < 1) || (l > 3)
                                                      then give_up ();
                                                      loc_sig _loc
                                                        (psig_value
                                                           ~attributes:(
                                                           attach_attrib _loc
                                                             a) _loc
                                                           (id_loc n _loc_n)
                                                           ty ls))
                               post_item_attributes))))));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun td  -> Sig.type_ ~loc:_loc Recursive td)
             type_definition;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun te  -> Sig.type_extension ~loc:_loc te)
             type_extension;
           Earley.fsequence exception_kw
             (Earley.apply_position
                (fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos
                            in
                         fun ((name,args,res,a) as _default_0)  ->
                           fun _default_1  ->
                             let cd =
                               Te.decl ~attrs:(attach_attrib _loc a)
                                 ~loc:_loc ~args ?res name
                                in
                             loc_sig _loc (Psig_exception cd))
                (constr_decl false));
           Earley.fsequence module_kw
             (Earley.fsequence rec_kw
                (Earley.fsequence
                   (Earley.apply_position
                      (fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  ->
                               fun x  -> ((locate str pos str' pos'), x))
                      module_name)
                   (Earley.fsequence (Earley.string ":" ":")
                      (Earley.fsequence module_type
                         (Earley.fsequence
                            (Earley.apply_position
                               (fun str  ->
                                  fun pos  ->
                                    fun str'  ->
                                      fun pos'  ->
                                        fun x  ->
                                          ((locate str pos str' pos'), x))
                               post_item_attributes)
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun ms  ->
                                          fun a  ->
                                            let (_loc_a,a) = a  in
                                            fun mt  ->
                                              fun _  ->
                                                fun mn  ->
                                                  let (_loc_mn,mn) = mn  in
                                                  fun _default_0  ->
                                                    fun _default_1  ->
                                                      let loc_first =
                                                        merge2 _loc_mn _loc_a
                                                         in
                                                      let m =
                                                        module_declaration
                                                          ~attributes:(
                                                          attach_attrib
                                                            loc_first a)
                                                          loc_first mn mt
                                                         in
                                                      loc_sig _loc
                                                        (Psig_recmodule (m ::
                                                           ms)))
                               (Earley.apply List.rev
                                  (Earley.fixpoint []
                                     (Earley.apply
                                        (fun x  -> fun y  -> x :: y)
                                        (Earley.fsequence and_kw
                                           (Earley.fsequence module_name
                                              (Earley.fsequence
                                                 (Earley.string ":" ":")
                                                 (Earley.fsequence
                                                    module_type
                                                    (Earley.apply_position
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
                                                                    __loc__end__pos
                                                                   in
                                                                fun a  ->
                                                                  fun mt  ->
                                                                    fun _  ->
                                                                    fun mn 
                                                                    ->
                                                                    fun
                                                                    _default_0
                                                                     ->
                                                                    module_declaration
                                                                    ~attributes:(
                                                                    attach_attrib
                                                                    _loc a)
                                                                    _loc mn
                                                                    mt)
                                                       post_item_attributes))))))))))))));
           Earley.fsequence module_kw
             (Earley.apply_position
                (fun __loc__start__buf  ->
                   fun __loc__start__pos  ->
                     fun __loc__end__buf  ->
                       fun __loc__end__pos  ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos
                            in
                         fun r  -> fun _default_0  -> loc_sig _loc r)
                (Earley.alternatives
                   [Earley.fsequence type_kw
                      (Earley.fsequence
                         (Earley.apply_position
                            (fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     fun x  ->
                                       ((locate str pos str' pos'), x))
                            modtype_name)
                         (Earley.fsequence
                            (Earley.option None
                               (Earley.apply (fun x  -> Some x)
                                  (Earley.fsequence (Earley.string "=" "=")
                                     (Earley.apply (fun mt  -> fun _  -> mt)
                                        module_type))))
                            (Earley.apply_position
                               (fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos
                                           in
                                        fun a  ->
                                          fun mt  ->
                                            fun mn  ->
                                              let (_loc_mn,mn) = mn  in
                                              fun _default_0  ->
                                                Psig_modtype
                                                  {
                                                    pmtd_name =
                                                      (id_loc mn _loc_mn);
                                                    pmtd_type = mt;
                                                    pmtd_attributes =
                                                      (attach_attrib _loc a);
                                                    pmtd_loc = _loc
                                                  }) post_item_attributes)));
                   Earley.fsequence module_name
                     (Earley.fsequence
                        (Earley.apply List.rev
                           (Earley.fixpoint []
                              (Earley.apply (fun x  -> fun y  -> x :: y)
                                 (Earley.fsequence (Earley.char '(' '(')
                                    (Earley.fsequence module_name
                                       (Earley.fsequence
                                          (Earley.option None
                                             (Earley.apply (fun x  -> Some x)
                                                (Earley.fsequence
                                                   (Earley.char ':' ':')
                                                   (Earley.apply
                                                      (fun mt  ->
                                                         fun _  -> mt)
                                                      module_type))))
                                          (Earley.apply_position
                                             (fun __loc__start__buf  ->
                                                fun __loc__start__pos  ->
                                                  fun __loc__end__buf  ->
                                                    fun __loc__end__pos  ->
                                                      let _loc =
                                                        locate
                                                          __loc__start__buf
                                                          __loc__start__pos
                                                          __loc__end__buf
                                                          __loc__end__pos
                                                         in
                                                      fun _  ->
                                                        fun mt  ->
                                                          fun mn  ->
                                                            fun _  ->
                                                              (mn, mt, _loc))
                                             (Earley.char ')' ')'))))))))
                        (Earley.fsequence (Earley.char ':' ':')
                           (Earley.fsequence
                              (Earley.apply_position
                                 (fun str  ->
                                    fun pos  ->
                                      fun str'  ->
                                        fun pos'  ->
                                          fun x  ->
                                            ((locate str pos str' pos'), x))
                                 module_type)
                              (Earley.apply_position
                                 (fun __loc__start__buf  ->
                                    fun __loc__start__pos  ->
                                      fun __loc__end__buf  ->
                                        fun __loc__end__pos  ->
                                          let _loc =
                                            locate __loc__start__buf
                                              __loc__start__pos
                                              __loc__end__buf __loc__end__pos
                                             in
                                          fun a  ->
                                            fun mt  ->
                                              let (_loc_mt,mt) = mt  in
                                              fun _  ->
                                                fun l  ->
                                                  fun mn  ->
                                                    let mt =
                                                      List.fold_left
                                                        (fun acc  ->
                                                           fun (mn,mt,_loc) 
                                                             ->
                                                             mtyp_loc
                                                               (merge2 _loc
                                                                  _loc_mt)
                                                               (Pmty_functor
                                                                  (mn, mt,
                                                                    acc))) mt
                                                        (List.rev l)
                                                       in
                                                    Psig_module
                                                      (module_declaration
                                                         ~attributes:(
                                                         attach_attrib _loc a)
                                                         _loc mn mt))
                                 post_item_attributes))))]));
           Earley.fsequence open_kw
             (Earley.fsequence override_flag
                (Earley.fsequence
                   (Earley.apply_position
                      (fun str  ->
                         fun pos  ->
                           fun str'  ->
                             fun pos'  ->
                               fun x  -> ((locate str pos str' pos'), x))
                      module_path)
                   (Earley.apply_position
                      (fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               fun a  ->
                                 fun m  ->
                                   let (_loc_m,m) = m  in
                                   fun o  ->
                                     fun _default_0  ->
                                       loc_sig _loc
                                         (Psig_open
                                            {
                                              popen_lid = (id_loc m _loc_m);
                                              popen_override = o;
                                              popen_loc = _loc;
                                              popen_attributes =
                                                (attach_attrib _loc a)
                                            })) post_item_attributes)));
           Earley.fsequence include_kw
             (Earley.fsequence module_type
                (Earley.apply_position
                   (fun __loc__start__buf  ->
                      fun __loc__start__pos  ->
                        fun __loc__end__buf  ->
                          fun __loc__end__pos  ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos
                               in
                            fun a  ->
                              fun me  ->
                                fun _default_0  ->
                                  loc_sig _loc
                                    (Psig_include
                                       {
                                         pincl_mod = me;
                                         pincl_loc = _loc;
                                         pincl_attributes =
                                           (attach_attrib _loc a)
                                       })) post_item_attributes));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ctd  -> loc_sig _loc (Psig_class_type ctd))
             classtype_definition;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun cs  -> loc_sig _loc (Psig_class cs))
             class_specification;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ((s,l) as _default_0)  ->
                        loc_sig _loc (Psig_attribute (s, l)))
             floating_attribute;
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun ((s,l) as _default_0)  ->
                        loc_sig _loc (Psig_extension ((s, l), [])))
             floating_extension])
      
    let _ =
      set_grammar signature_item
        (Earley.alternatives
           [Earley.fsequence signature_item_base
              (Earley.apply_position
                 (fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          fun _  -> fun s  -> (attach_sig _loc) @ [s])
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x) double_semi_col)));
           Earley.apply_position
             (fun __loc__start__buf  ->
                fun __loc__start__pos  ->
                  fun __loc__end__buf  ->
                    fun __loc__end__pos  ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos
                         in
                      fun e  -> (attach_sig _loc) @ e)
             (alternatives extra_signature)])
      
  end
