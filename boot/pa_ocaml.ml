open Earley_core
open Input
open Earley
open Charset
open Ast_helper
open Asttypes
open Parsetree
open Longident
open Pa_lexing
open Ast_helper
include Pa_ocaml_prelude
let ghost loc = let open Location in { loc with loc_ghost = true }
let no_ghost loc = let open Location in { loc with loc_ghost = false }
let de_ghost e = Exp.mk ~loc:(no_ghost e.pexp_loc) e.pexp_desc
let id_loc txt loc = { txt; loc }
let loc_id loc txt = { txt; loc }
let merge2 l1 l2 =
  let loc_ghost = let open Location in l1.loc_ghost && l2.loc_ghost in
  let open Location in { l1 with loc_end = (l2.loc_end); loc_ghost }
let exp_apply loc f l = Exp.apply ~loc f (List.map (fun x -> (Nolabel, x)) l)
let ouident = uident
let uident = Earley_core.Earley.declare_grammar "uident"
let _ = Earley_core.Earley.set_grammar uident ouident
let olident = lident
let lident = Earley_core.Earley.declare_grammar "lident"
let _ = Earley_core.Earley.set_grammar lident olident
let oident = ident
let ident = Earley_core.Earley.declare_grammar "ident"
let _ = Earley_core.Earley.set_grammar ident oident
let mk_unary_op loc name loc_name arg =
  match (name, (arg.pexp_desc)) with
  | ("-", Pexp_constant (Pconst_integer (n, o))) ->
      Exp.constant ~loc (Const.integer ?suffix:o ("-" ^ n))
  | (("-"|"-."), Pexp_constant (Pconst_float (f, o))) ->
      Exp.constant ~loc (Const.float ?suffix:o ("-" ^ f))
  | ("+", Pexp_constant (Pconst_integer _))
    |(("+"|"+."), Pexp_constant (Pconst_float _)) ->
      Exp.mk ~loc arg.pexp_desc
  | (("-"|"-."|"+"|"+."), _) ->
      let lid = id_loc (Lident ("~" ^ name)) loc_name in
      let fn = Exp.ident ~loc:loc_name lid in
      Exp.apply ~loc fn [(Nolabel, arg)]
  | _ ->
      let lid = id_loc (Lident name) loc_name in
      let fn = Exp.ident ~loc:loc_name lid in
      Exp.apply ~loc fn [(Nolabel, arg)]
let mk_binary_op loc e' op loc_op e =
  if op = "::"
  then
    let lid = id_loc (Lident "::") loc_op in
    Exp.construct ~loc lid (Some (Exp.tuple ~loc:(ghost loc) [e'; e]))
  else
    (let id = Exp.ident ~loc:loc_op (id_loc (Lident op) loc_op) in
     Exp.apply ~loc id [(Nolabel, e'); (Nolabel, e)])
let wrap_type_annotation loc types core_type body =
  let exp = Exp.constraint_ ~loc body core_type in
  let exp =
    List.fold_right (fun ty -> fun exp -> Exp.newtype ~loc ty exp) types exp in
  (exp,
    (Typ.poly ~loc:(ghost loc) types
       (Typ.varify_constructors types core_type)))
type tree =
  | Node of tree * tree 
  | Leaf of string 
let string_of_tree (t : tree) =
  (let b = Buffer.create 101 in
   let rec fn =
     function | Leaf s -> Buffer.add_string b s | Node (a, b) -> (fn a; fn b) in
   fn t; Buffer.contents b : string)
let label_name = lident
let ty_label = Earley_core.Earley.declare_grammar "ty_label"
let _ =
  Earley_core.Earley.set_grammar ty_label
    (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '~' '~')
       (Earley_core.Earley.fsequence_ignore
          (Earley_core.Earley.no_blank_test ())
          (Earley_core.Earley.fsequence lident
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ':' ':')
                (Earley_core.Earley.empty (fun s -> Labelled s))))))
let ty_opt_label = Earley_core.Earley.declare_grammar "ty_opt_label"
let _ =
  Earley_core.Earley.set_grammar ty_opt_label
    (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '?' '?')
       (Earley_core.Earley.fsequence_ignore
          (Earley_core.Earley.no_blank_test ())
          (Earley_core.Earley.fsequence lident
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ':' ':')
                (Earley_core.Earley.empty (fun s -> Optional s))))))
let maybe_opt_label = Earley_core.Earley.declare_grammar "maybe_opt_label"
let _ =
  Earley_core.Earley.set_grammar maybe_opt_label
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.char '?' '?')))
       (Earley_core.Earley.fsequence label_name
          (Earley_core.Earley.empty
             (fun ln ->
                fun o -> if o = None then Labelled ln else Optional ln))))
let operator_name =
  alternatives ((prefix_symbol Prefix) ::
    (List.map infix_symbol infix_prios))
let value_name = Earley_core.Earley.declare_grammar "value_name"
let _ =
  Earley_core.Earley.set_grammar value_name
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '(' '(')
             (Earley_core.Earley.fsequence operator_name
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ')' ')')
                   (Earley_core.Earley.empty (fun op -> op)))))
          (List.cons lident [])))
let constr_name = uident
let tag_name = Earley_core.Earley.declare_grammar "tag_name"
let _ =
  Earley_core.Earley.set_grammar tag_name
    (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.string "`" "`")
       (Earley_core.Earley.fsequence ident
          (Earley_core.Earley.empty (fun c -> c))))
let typeconstr_name = lident
let field_name = lident
let smodule_name = uident
let module_name = Earley_core.Earley.declare_grammar "module_name"
let _ =
  Earley_core.Earley.set_grammar module_name
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence joker_kw
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun _default_0 -> id_loc None _loc)))
          (List.cons
             (Earley_core.Earley.fsequence uident
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun u -> id_loc (Some u) _loc))) [])))
let modtype_name = ident
let class_name = lident
let inst_var_name = lident
let method_name = Earley_core.Earley.declare_grammar "method_name"
let _ =
  Earley_core.Earley.set_grammar method_name
    (Earley_core.Earley.fsequence lident
       (Earley_core.Earley.empty_pos
          (fun __loc__start__buf ->
             fun __loc__start__pos ->
               fun __loc__end__buf ->
                 fun __loc__end__pos ->
                   let _loc =
                     locate __loc__start__buf __loc__start__pos
                       __loc__end__buf __loc__end__pos in
                   fun id -> id_loc id _loc)))
let (module_path_gen, set_module_path_gen) = grammar_family "module_path_gen"
let (module_path_suit, set_module_path_suit) =
  grammar_family "module_path_suit"
let (module_path_suit_aux, module_path_suit_aux__set__grammar) =
  Earley_core.Earley.grammar_family "module_path_suit_aux"
let _ =
  module_path_suit_aux__set__grammar
    (fun allow_app ->
       Earley_core.Earley.alternatives
         (List.cons
            (Earley_core.Earley.fsequence_ignore
               (Earley_core.Earley.string "." ".")
               (Earley_core.Earley.fsequence smodule_name
                  (Earley_core.Earley.empty
                     (fun m -> fun acc -> Ldot (acc, m)))))
            (List.append
               (if allow_app
                then
                  List.cons
                    (Earley_core.Earley.fsequence_ignore
                       (Earley_core.Earley.string "(" "(")
                       (Earley_core.Earley.fsequence (module_path_gen true)
                          (Earley_core.Earley.fsequence_ignore
                             (Earley_core.Earley.string ")" ")")
                             (Earley_core.Earley.empty
                                (fun m' -> fun a -> Lapply (a, m')))))) []
                else []) [])))
let _ =
  set_module_path_suit
    (fun allow_app ->
       Earley_core.Earley.alternatives
         (List.cons
            (Earley_core.Earley.fsequence_ignore
               (Earley_core.Earley.empty ())
               (Earley_core.Earley.empty (fun acc -> acc)))
            (List.cons
               (Earley_core.Earley.fsequence (module_path_suit_aux allow_app)
                  (Earley_core.Earley.fsequence (module_path_suit allow_app)
                     (Earley_core.Earley.empty
                        (fun g -> fun f -> fun acc -> g (f acc))))) [])))
let _ =
  set_module_path_gen
    (fun allow_app ->
       Earley_core.Earley.fsequence smodule_name
         (Earley_core.Earley.fsequence (module_path_suit allow_app)
            (Earley_core.Earley.empty (fun s -> fun m -> s (Lident m)))))
let module_path = module_path_gen false
let extended_module_path = module_path_gen true
let _ =
  set_grammar value_path
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence value_name
          (Earley_core.Earley.empty
             (fun vn ->
                fun mp ->
                  match mp with | None -> Lident vn | Some p -> Ldot (p, vn)))))
let constr = Earley_core.Earley.declare_grammar "constr"
let _ =
  Earley_core.Earley.set_grammar constr
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence constr_name
          (Earley_core.Earley.empty
             (fun cn ->
                fun mp ->
                  match mp with | None -> Lident cn | Some p -> Ldot (p, cn)))))
let typeconstr = Earley_core.Earley.declare_grammar "typeconstr"
let _ =
  Earley_core.Earley.set_grammar typeconstr
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence extended_module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence typeconstr_name
          (Earley_core.Earley.empty
             (fun tcn ->
                fun mp ->
                  match mp with
                  | None -> Lident tcn
                  | Some p -> Ldot (p, tcn)))))
let field = Earley_core.Earley.declare_grammar "field"
let _ =
  Earley_core.Earley.set_grammar field
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence field_name
          (Earley_core.Earley.empty
             (fun fn ->
                fun mp ->
                  match mp with | None -> Lident fn | Some p -> Ldot (p, fn)))))
let class_path = Earley_core.Earley.declare_grammar "class_path"
let _ =
  Earley_core.Earley.set_grammar class_path
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence class_name
          (Earley_core.Earley.empty
             (fun cn ->
                fun mp ->
                  match mp with | None -> Lident cn | Some p -> Ldot (p, cn)))))
let modtype_path = Earley_core.Earley.declare_grammar "modtype_path"
let _ =
  Earley_core.Earley.set_grammar modtype_path
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence extended_module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence modtype_name
          (Earley_core.Earley.empty
             (fun mtn ->
                fun mp ->
                  match mp with
                  | None -> Lident mtn
                  | Some p -> Ldot (p, mtn)))))
let classtype_path = Earley_core.Earley.declare_grammar "classtype_path"
let _ =
  Earley_core.Earley.set_grammar classtype_path
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence extended_module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence class_name
          (Earley_core.Earley.empty
             (fun cn ->
                fun mp ->
                  match mp with | None -> Lident cn | Some p -> Ldot (p, cn)))))
let opt_variance = Earley_core.Earley.declare_grammar "opt_variance"
let _ =
  Earley_core.Earley.set_grammar opt_variance
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_str.regexp "[+-]" (fun group -> group 0))))
       (Earley_core.Earley.empty
          (fun v ->
             match v with
             | None -> Invariant
             | Some "+" -> Covariant
             | Some "-" -> Contravariant
             | _ -> assert false)))
let override_flag = Earley_core.Earley.declare_grammar "override_flag"
let _ =
  Earley_core.Earley.set_grammar override_flag
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.string "!" "!")))
       (Earley_core.Earley.empty
          (fun o -> if o <> None then Override else Fresh)))
let attr_id = Earley_core.Earley.declare_grammar "attr_id"
let _ =
  Earley_core.Earley.set_grammar attr_id
    (Earley_core.Earley.fsequence ident
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l)
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '.' '.')
                   (Earley_core.Earley.fsequence ident
                      (Earley_core.Earley.empty (fun id -> id))))
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.empty_pos
             (fun __loc__start__buf ->
                fun __loc__start__pos ->
                  fun __loc__end__buf ->
                    fun __loc__end__pos ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      fun l ->
                        fun id -> id_loc (String.concat "." (id :: l)) _loc))))
let payload = Earley_core.Earley.declare_grammar "payload"
let _ =
  Earley_core.Earley.set_grammar payload
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '?' '?')
             (Earley_core.Earley.fsequence pattern
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.option None
                      (Earley_core.Earley.apply (fun x -> Some x)
                         (Earley_core.Earley.fsequence_ignore when_kw
                            (Earley_core.Earley.fsequence expression
                               (Earley_core.Earley.empty (fun e -> e))))))
                   (Earley_core.Earley.empty (fun e -> fun p -> PPat (p, e))))))
          (List.cons
             (Earley_core.Earley.fsequence structure
                (Earley_core.Earley.empty (fun s -> PStr s)))
             (List.cons
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ':' ':')
                   (Earley_core.Earley.fsequence typexpr
                      (Earley_core.Earley.empty (fun t -> PTyp t)))) []))))
let attribute = Earley_core.Earley.declare_grammar "attribute"
let _ =
  Earley_core.Earley.set_grammar attribute
    (Earley_core.Earley.fsequence_ignore
       (Earley_core.Earley.string "[@" "[@")
       (Earley_core.Earley.fsequence attr_id
          (Earley_core.Earley.fsequence payload
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ']' ']')
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun p -> fun id -> Attr.mk ~loc:_loc id p))))))
let attributes = Earley_core.Earley.declare_grammar "attributes"
let _ =
  Earley_core.Earley.set_grammar attributes
    (Earley_core.Earley.apply (fun f -> f [])
       (Earley_core.Earley.fixpoint' (fun l -> l) attribute
          (fun x -> fun f -> fun l -> f (List.cons x l))))
let ext_attributes = Earley_core.Earley.declare_grammar "ext_attributes"
let _ =
  Earley_core.Earley.set_grammar ext_attributes
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '%' '%')
                (Earley_core.Earley.fsequence attribute
                   (Earley_core.Earley.empty (fun a -> a))))))
       (Earley_core.Earley.fsequence attributes
          (Earley_core.Earley.empty (fun l -> fun a -> (a, l)))))
let post_item_attributes =
  Earley_core.Earley.declare_grammar "post_item_attributes"
let _ =
  Earley_core.Earley.set_grammar post_item_attributes
    (Earley_core.Earley.apply (fun f -> f [])
       (Earley_core.Earley.fixpoint' (fun l -> l)
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.string "[@@" "[@@")
             (Earley_core.Earley.fsequence attr_id
                (Earley_core.Earley.fsequence payload
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char ']' ']')
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun p -> fun id -> Attr.mk ~loc:_loc id p))))))
          (fun x -> fun f -> fun l -> f (List.cons x l))))
let floating_attribute =
  Earley_core.Earley.declare_grammar "floating_attribute"
let _ =
  Earley_core.Earley.set_grammar floating_attribute
    (Earley_core.Earley.fsequence_ignore
       (Earley_core.Earley.string "[@@@" "[@@@")
       (Earley_core.Earley.fsequence attr_id
          (Earley_core.Earley.fsequence payload
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ']' ']')
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun p -> fun id -> Attr.mk ~loc:_loc id p))))))
let extension = Earley_core.Earley.declare_grammar "extension"
let _ =
  Earley_core.Earley.set_grammar extension
    (Earley_core.Earley.fsequence_ignore
       (Earley_core.Earley.string "[%" "[%")
       (Earley_core.Earley.fsequence attr_id
          (Earley_core.Earley.fsequence payload
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ']' ']')
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun p -> fun id -> Attr.mk ~loc:_loc id p))))))
let floating_extension =
  Earley_core.Earley.declare_grammar "floating_extension"
let _ =
  Earley_core.Earley.set_grammar floating_extension
    (Earley_core.Earley.fsequence_ignore
       (Earley_core.Earley.string "[%%" "[%%")
       (Earley_core.Earley.fsequence attr_id
          (Earley_core.Earley.fsequence payload
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ']' ']')
                (Earley_core.Earley.empty (fun p -> fun id -> (id, p)))))))
let only_poly_typexpr =
  Earley_core.Earley.declare_grammar "only_poly_typexpr"
let _ =
  Earley_core.Earley.set_grammar only_poly_typexpr
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.apply (fun f -> f [])
          (Earley_core.Earley.fixpoint1' (fun l -> l)
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '\'' '\'')
                (Earley_core.Earley.fsequence ident
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun id -> id_loc id _loc))))
             (fun x -> fun f -> fun l -> f (List.cons x l))))
       (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '.' '.')
          (Earley_core.Earley.fsequence typexpr
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun te -> fun ids -> Typ.poly ~loc:_loc ids te)))))
let poly_typexpr = Earley_core.Earley.declare_grammar "poly_typexpr"
let _ =
  Earley_core.Earley.set_grammar poly_typexpr
    (Earley_core.Earley.alternatives
       (List.cons typexpr
          (List.cons
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.apply (fun f -> f [])
                   (Earley_core.Earley.fixpoint1' (fun l -> l)
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '\'' '\'')
                         (Earley_core.Earley.fsequence ident
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun id -> id_loc id _loc))))
                      (fun x -> fun f -> fun l -> f (List.cons x l))))
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '.' '.')
                   (Earley_core.Earley.fsequence typexpr
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun te ->
                                    fun ids -> Typ.poly ~loc:_loc ids te)))))
             [])))
let poly_syntax_typexpr =
  Earley_core.Earley.declare_grammar "poly_syntax_typexpr"
let _ =
  Earley_core.Earley.set_grammar poly_syntax_typexpr
    (Earley_core.Earley.fsequence type_kw
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint1' (fun l -> l)
                (Earley_core.Earley.fsequence_position typeconstr_name
                   (Earley_core.Earley.empty
                      (fun str1 ->
                         fun pos1 ->
                           fun str2 ->
                             fun pos2 ->
                               fun id ->
                                 let _loc_id = locate str1 pos1 str2 pos2 in
                                 id_loc id _loc_id)))
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '.' '.')
             (Earley_core.Earley.fsequence typexpr
                (Earley_core.Earley.empty
                   (fun te -> fun ids -> fun _default_0 -> (ids, te)))))))
let method_type = Earley_core.Earley.declare_grammar "method_type"
let _ =
  Earley_core.Earley.set_grammar method_type
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence
             (typexpr_lvl (next_type_prio DashType))
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun ty -> Of.inherit_ ~loc:_loc ty)))
          (List.cons
             (Earley_core.Earley.fsequence method_name
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ':' ':')
                   (Earley_core.Earley.fsequence poly_typexpr
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun pte ->
                                    fun mn -> Of.tag ~loc:_loc mn pte))))) [])))
let tag_spec = Earley_core.Earley.declare_grammar "tag_spec"
let _ =
  Earley_core.Earley.set_grammar tag_spec
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence typexpr
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun te -> Rf.inherit_ ~loc:_loc te)))
          (List.cons
             (Earley_core.Earley.fsequence_position tag_name
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.option None
                      (Earley_core.Earley.apply (fun x -> Some x)
                         (Earley_core.Earley.fsequence_ignore of_kw
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.option None
                                  (Earley_core.Earley.apply (fun x -> Some x)
                                     (Earley_core.Earley.char '&' '&')))
                               (Earley_core.Earley.fsequence typexpr
                                  (Earley_core.Earley.empty
                                     (fun _default_0 ->
                                        fun _default_1 ->
                                          (_default_1, _default_0))))))))
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun te ->
                                 fun str1 ->
                                   fun pos1 ->
                                     fun str2 ->
                                       fun pos2 ->
                                         fun tn ->
                                           let _loc_tn =
                                             locate str1 pos1 str2 pos2 in
                                           let (amp, t) =
                                             match te with
                                             | None -> (true, [])
                                             | Some (amp, l) ->
                                                 ((amp <> None), [l]) in
                                           let tn = id_loc tn _loc_tn in
                                           Rf.tag ~loc:_loc tn amp t)))) [])))
let tag_spec_first = Earley_core.Earley.declare_grammar "tag_spec_first"
let _ =
  Earley_core.Earley.set_grammar tag_spec_first
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.option None
                (Earley_core.Earley.apply (fun x -> Some x) typexpr))
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '|' '|')
                (Earley_core.Earley.fsequence tag_spec
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun ts ->
                                 fun te ->
                                   match te with
                                   | None -> [ts]
                                   | Some te ->
                                       [Rf.inherit_ ~loc:_loc te; ts])))))
          (List.cons
             (Earley_core.Earley.fsequence_position tag_name
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.option None
                      (Earley_core.Earley.apply (fun x -> Some x)
                         (Earley_core.Earley.fsequence_ignore of_kw
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.option None
                                  (Earley_core.Earley.apply (fun x -> Some x)
                                     (Earley_core.Earley.char '&' '&')))
                               (Earley_core.Earley.fsequence typexpr
                                  (Earley_core.Earley.empty
                                     (fun _default_0 ->
                                        fun _default_1 ->
                                          (_default_1, _default_0))))))))
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun te ->
                                 fun str1 ->
                                   fun pos1 ->
                                     fun str2 ->
                                       fun pos2 ->
                                         fun tn ->
                                           let _loc_tn =
                                             locate str1 pos1 str2 pos2 in
                                           let (amp, t) =
                                             match te with
                                             | None -> (true, [])
                                             | Some (amp, l) ->
                                                 ((amp <> None), [l]) in
                                           let tn = id_loc tn _loc_tn in
                                           [Rf.tag ~loc:_loc tn amp t])))) [])))
let tag_spec_full = Earley_core.Earley.declare_grammar "tag_spec_full"
let _ =
  Earley_core.Earley.set_grammar tag_spec_full
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence typexpr
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun te -> Rf.inherit_ ~loc:_loc te)))
          (List.cons
             (Earley_core.Earley.fsequence_position tag_name
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.option (true, [])
                      (Earley_core.Earley.fsequence of_kw
                         (Earley_core.Earley.fsequence
                            (Earley_core.Earley.option None
                               (Earley_core.Earley.apply (fun x -> Some x)
                                  (Earley_core.Earley.char '&' '&')))
                            (Earley_core.Earley.fsequence typexpr
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.apply (fun f -> f [])
                                     (Earley_core.Earley.fixpoint'
                                        (fun l -> l)
                                        (Earley_core.Earley.fsequence_ignore
                                           (Earley_core.Earley.char '&' '&')
                                           (Earley_core.Earley.fsequence
                                              typexpr
                                              (Earley_core.Earley.empty
                                                 (fun te -> te))))
                                        (fun x ->
                                           fun f ->
                                             fun l -> f (List.cons x l))))
                                  (Earley_core.Earley.empty
                                     (fun tes ->
                                        fun te ->
                                          fun amp ->
                                            fun _default_0 ->
                                              ((amp <> None), (te :: tes)))))))))
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun ((amp, tes) as _default_0) ->
                                 fun str1 ->
                                   fun pos1 ->
                                     fun str2 ->
                                       fun pos2 ->
                                         fun tn ->
                                           let _loc_tn =
                                             locate str1 pos1 str2 pos2 in
                                           let tn = id_loc tn _loc_tn in
                                           Rf.tag ~loc:_loc tn amp tes)))) [])))
let polymorphic_variant_type =
  Earley_core.Earley.declare_grammar "polymorphic_variant_type"
let _ =
  Earley_core.Earley.set_grammar polymorphic_variant_type
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.string "[<" "[<")
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.option None
                   (Earley_core.Earley.apply (fun x -> Some x)
                      (Earley_core.Earley.char '|' '|')))
                (Earley_core.Earley.fsequence tag_spec_full
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.apply (fun f -> f [])
                         (Earley_core.Earley.fixpoint' (fun l -> l)
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '|' '|')
                               (Earley_core.Earley.fsequence tag_spec_full
                                  (Earley_core.Earley.empty (fun tsf -> tsf))))
                            (fun x -> fun f -> fun l -> f (List.cons x l))))
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.option []
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '>' '>')
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.apply (fun f -> f [])
                                     (Earley_core.Earley.fixpoint1'
                                        (fun l -> l) tag_name
                                        (fun x ->
                                           fun f ->
                                             fun l -> f (List.cons x l))))
                                  (Earley_core.Earley.empty (fun tns -> tns)))))
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ']' ']')
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun tns ->
                                          fun tfss ->
                                            fun tfs ->
                                              fun _default_0 ->
                                                Typ.variant ~loc:_loc (tfs ::
                                                  tfss) Closed (Some tns)))))))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '[' '[')
                (Earley_core.Earley.fsequence tag_spec_first
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.apply (fun f -> f [])
                         (Earley_core.Earley.fixpoint' (fun l -> l)
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '|' '|')
                               (Earley_core.Earley.fsequence tag_spec
                                  (Earley_core.Earley.empty (fun ts -> ts))))
                            (fun x -> fun f -> fun l -> f (List.cons x l))))
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char ']' ']')
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun tss ->
                                       fun tsf ->
                                         Typ.variant ~loc:_loc (tsf @ tss)
                                           Closed None))))))
             (List.cons
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "[>" "[>")
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x) tag_spec))
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.apply (fun f -> f [])
                            (Earley_core.Earley.fixpoint' (fun l -> l)
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char '|' '|')
                                  (Earley_core.Earley.fsequence tag_spec
                                     (Earley_core.Earley.empty (fun ts -> ts))))
                               (fun x -> fun f -> fun l -> f (List.cons x l))))
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ']' ']')
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun tss ->
                                          fun ts ->
                                            let tss =
                                              match ts with
                                              | None -> tss
                                              | Some ts -> ts :: tss in
                                            Typ.variant ~loc:_loc tss Open
                                              None)))))) []))) : core_type
                                                                   grammar)
let package_constraint =
  Earley_core.Earley.declare_grammar "package_constraint"
let _ =
  Earley_core.Earley.set_grammar package_constraint
    (Earley_core.Earley.fsequence type_kw
       (Earley_core.Earley.fsequence_position typeconstr
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '=' '=')
             (Earley_core.Earley.fsequence typexpr
                (Earley_core.Earley.empty
                   (fun te ->
                      fun str1 ->
                        fun pos1 ->
                          fun str2 ->
                            fun pos2 ->
                              fun tc ->
                                let _loc_tc = locate str1 pos1 str2 pos2 in
                                fun _default_0 ->
                                  let tc = id_loc tc _loc_tc in (tc, te)))))))
let package_type = Earley_core.Earley.declare_grammar "package_type"
let _ =
  Earley_core.Earley.set_grammar package_type
    (Earley_core.Earley.fsequence_position modtype_path
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.option []
             (Earley_core.Earley.fsequence with_kw
                (Earley_core.Earley.fsequence package_constraint
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.apply (fun f -> f [])
                         (Earley_core.Earley.fixpoint' (fun l -> l)
                            (Earley_core.Earley.fsequence_ignore and_kw
                               (Earley_core.Earley.fsequence
                                  package_constraint
                                  (Earley_core.Earley.empty
                                     (fun _default_0 -> _default_0))))
                            (fun x -> fun f -> fun l -> f (List.cons x l))))
                      (Earley_core.Earley.empty
                         (fun pcs -> fun pc -> fun _default_0 -> pc :: pcs))))))
          (Earley_core.Earley.empty_pos
             (fun __loc__start__buf ->
                fun __loc__start__pos ->
                  fun __loc__end__buf ->
                    fun __loc__end__pos ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      fun cs ->
                        fun str1 ->
                          fun pos1 ->
                            fun str2 ->
                              fun pos2 ->
                                fun mtp ->
                                  let _loc_mtp = locate str1 pos1 str2 pos2 in
                                  Typ.package ~loc:_loc (id_loc mtp _loc_mtp)
                                    cs))))
let opt_present = Earley_core.Earley.declare_grammar "opt_present"
let _ =
  Earley_core.Earley.set_grammar opt_present
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty []))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "[>" "[>")
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.apply (fun f -> f [])
                      (Earley_core.Earley.fixpoint1' (fun l -> l) tag_name
                         (fun x -> fun f -> fun l -> f (List.cons x l))))
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.string "]" "]")
                      (Earley_core.Earley.empty (fun l -> l))))) [])))
let mkoption loc d =
  let loc = ghost loc in
  Typ.constr ~loc (id_loc (Ldot ((Lident "*predef*"), "option")) loc) [d]
let op_cl =
  Earley_core.Earley.alternatives
    (List.cons
       (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
          (Earley_core.Earley.empty Closed))
       (List.cons
          (Earley_core.Earley.fsequence (Earley_core.Earley.string ".." "..")
             (Earley_core.Earley.empty (fun d -> Open))) []))
let _ =
  set_typexpr_lvl
    ((List.cons
        ((fun (allow_par, lvl) -> lvl <= As),
          (Earley_core.Earley.fsequence (typexpr_lvl As)
             (Earley_core.Earley.fsequence as_kw
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '\'' '\'')
                   (Earley_core.Earley.fsequence ident
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun id ->
                                    fun _default_0 ->
                                      fun te -> Typ.alias ~loc:_loc te id)))))))
        (List.cons
           ((fun _ -> true),
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "'" "'")
                (Earley_core.Earley.fsequence ident
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun id -> Typ.var ~loc:_loc id)))))
           (List.cons
              ((fun _ -> true),
                (Earley_core.Earley.fsequence joker_kw
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun _default_0 -> Typ.any ~loc:_loc ()))))
              (List.cons
                 ((fun _ -> true),
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '(' '(')
                      (Earley_core.Earley.fsequence module_kw
                         (Earley_core.Earley.fsequence package_type
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char ')' ')')
                               (Earley_core.Earley.empty_pos
                                  (fun __loc__start__buf ->
                                     fun __loc__start__pos ->
                                       fun __loc__end__buf ->
                                         fun __loc__end__pos ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           fun pt ->
                                             fun _default_0 ->
                                               Typ.mk ~loc:_loc pt.ptyp_desc)))))))
                 (List.cons
                    ((fun (allow_par, lvl) -> allow_par),
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '(' '(')
                         (Earley_core.Earley.fsequence typexpr
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.apply (fun f -> f [])
                                  (Earley_core.Earley.fixpoint' (fun l -> l)
                                     attribute
                                     (fun x ->
                                        fun f -> fun l -> f (List.cons x l))))
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ')' ')')
                                  (Earley_core.Earley.empty
                                     (fun at ->
                                        fun te ->
                                          { te with ptyp_attributes = at })))))))
                    (List.cons
                       ((fun (allow_par, lvl) -> lvl <= Arr),
                         (Earley_core.Earley.fsequence ty_opt_label
                            (Earley_core.Earley.fsequence
                               (typexpr_lvl ProdType)
                               (Earley_core.Earley.fsequence arrow_re
                                  (Earley_core.Earley.fsequence
                                     (typexpr_lvl Arr)
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun te' ->
                                                   fun _default_0 ->
                                                     fun te ->
                                                       fun ln ->
                                                         Typ.arrow ~loc:_loc
                                                           ln te te')))))))
                       (List.cons
                          ((fun (allow_par, lvl) -> lvl <= Arr),
                            (Earley_core.Earley.fsequence label_name
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ':' ':')
                                  (Earley_core.Earley.fsequence
                                     (typexpr_lvl ProdType)
                                     (Earley_core.Earley.fsequence arrow_re
                                        (Earley_core.Earley.fsequence
                                           (typexpr_lvl Arr)
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun te' ->
                                                         fun _default_0 ->
                                                           fun te ->
                                                             fun ln ->
                                                               Typ.arrow
                                                                 ~loc:_loc
                                                                 (Labelled ln)
                                                                 te te'))))))))
                          (List.cons
                             ((fun (allow_par, lvl) -> lvl <= Arr),
                               (Earley_core.Earley.fsequence
                                  (typexpr_lvl ProdType)
                                  (Earley_core.Earley.fsequence arrow_re
                                     (Earley_core.Earley.fsequence
                                        (typexpr_lvl Arr)
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun te' ->
                                                      fun _default_0 ->
                                                        fun te ->
                                                          Typ.arrow ~loc:_loc
                                                            Nolabel te te'))))))
                             (List.cons
                                ((fun _ -> true),
                                  (Earley_core.Earley.fsequence_position
                                     typeconstr
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun str1 ->
                                                   fun pos1 ->
                                                     fun str2 ->
                                                       fun pos2 ->
                                                         fun tc ->
                                                           let _loc_tc =
                                                             locate str1 pos1
                                                               str2 pos2 in
                                                           Typ.constr
                                                             ~loc:_loc
                                                             (id_loc tc
                                                                _loc_tc) []))))
                                (List.cons
                                   ((fun (allow_par, lvl) -> lvl <= AppType),
                                     (Earley_core.Earley.fsequence_ignore
                                        (Earley_core.Earley.char '(' '(')
                                        (Earley_core.Earley.fsequence typexpr
                                           (Earley_core.Earley.fsequence
                                              (Earley_core.Earley.apply
                                                 (fun f -> f [])
                                                 (Earley_core.Earley.fixpoint1'
                                                    (fun l -> l)
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.char
                                                          ',' ',')
                                                       (Earley_core.Earley.fsequence
                                                          typexpr
                                                          (Earley_core.Earley.empty
                                                             (fun te -> te))))
                                                    (fun x ->
                                                       fun f ->
                                                         fun l ->
                                                           f (List.cons x l))))
                                              (Earley_core.Earley.fsequence_ignore
                                                 (Earley_core.Earley.char ')'
                                                    ')')
                                                 (Earley_core.Earley.fsequence_position
                                                    typeconstr
                                                    (Earley_core.Earley.empty_pos
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
                                                                    __loc__end__pos in
                                                                fun str1 ->
                                                                  fun pos1 ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun tc ->
                                                                    let _loc_tc
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun tes
                                                                    ->
                                                                    fun te ->
                                                                    Typ.constr
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    tc
                                                                    _loc_tc)
                                                                    (te ::
                                                                    tes)))))))))
                                   (List.cons
                                      ((fun (allow_par, lvl) ->
                                          lvl <= AppType),
                                        (Earley_core.Earley.fsequence
                                           (typexpr_lvl AppType)
                                           (Earley_core.Earley.fsequence_position
                                              typeconstr
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun str1 ->
                                                            fun pos1 ->
                                                              fun str2 ->
                                                                fun pos2 ->
                                                                  fun tc ->
                                                                    let _loc_tc
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun t ->
                                                                    Typ.constr
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    tc
                                                                    _loc_tc)
                                                                    [t])))))
                                      (List.cons
                                         ((fun _ -> true),
                                           polymorphic_variant_type)
                                         (List.cons
                                            ((fun _ -> true),
                                              (Earley_core.Earley.fsequence_ignore
                                                 (Earley_core.Earley.char '<'
                                                    '<')
                                                 (Earley_core.Earley.fsequence
                                                    op_cl
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.char
                                                          '>' '>')
                                                       (Earley_core.Earley.empty_pos
                                                          (fun
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
                                                                   fun rv ->
                                                                    Typ.object_
                                                                    ~loc:_loc
                                                                    [] rv))))))
                                            (List.cons
                                               ((fun _ -> true),
                                                 (Earley_core.Earley.fsequence_ignore
                                                    (Earley_core.Earley.char
                                                       '<' '<')
                                                    (Earley_core.Earley.fsequence
                                                       (Earley.list1
                                                          method_type
                                                          semi_col)
                                                       (Earley_core.Earley.fsequence
                                                          (Earley_core.Earley.option
                                                             Closed
                                                             (Earley_core.Earley.fsequence_ignore
                                                                semi_col
                                                                (Earley_core.Earley.fsequence
                                                                   op_cl
                                                                   (Earley_core.Earley.empty
                                                                    (fun
                                                                    _default_0
                                                                    ->
                                                                    _default_0)))))
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.char
                                                                '>' '>')
                                                             (Earley_core.Earley.empty_pos
                                                                (fun
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
                                                                    fun rv ->
                                                                    fun mts
                                                                    ->
                                                                    Typ.object_
                                                                    ~loc:_loc
                                                                    mts rv)))))))
                                               (List.cons
                                                  ((fun _ -> true),
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.char
                                                          '#' '#')
                                                       (Earley_core.Earley.fsequence_position
                                                          class_path
                                                          (Earley_core.Earley.empty_pos
                                                             (fun
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
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun cp ->
                                                                    let _loc_cp
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    Typ.class_
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    cp
                                                                    _loc_cp)
                                                                    [])))))
                                                  (List.cons
                                                     ((fun (allow_par, lvl)
                                                         -> lvl <= DashType),
                                                       (Earley_core.Earley.fsequence
                                                          (typexpr_lvl
                                                             DashType)
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.char
                                                                '#' '#')
                                                             (Earley_core.Earley.fsequence_position
                                                                class_path
                                                                (Earley_core.Earley.empty_pos
                                                                   (fun
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
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun cp ->
                                                                    let _loc_cp
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun te ->
                                                                    Typ.class_
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    cp
                                                                    _loc_cp)
                                                                    [te]))))))
                                                     (List.cons
                                                        ((fun _ -> true),
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.char
                                                                '(' '(')
                                                             (Earley_core.Earley.fsequence
                                                                typexpr
                                                                (Earley_core.Earley.fsequence
                                                                   (Earley_core.Earley.apply
                                                                    (fun f ->
                                                                    f [])
                                                                    (Earley_core.Earley.fixpoint'
                                                                    (fun l ->
                                                                    l)
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ',' ',')
                                                                    (Earley_core.Earley.fsequence
                                                                    typexpr
                                                                    (Earley_core.Earley.empty
                                                                    (fun te
                                                                    -> te))))
                                                                    (fun x ->
                                                                    fun f ->
                                                                    fun l ->
                                                                    f
                                                                    (List.cons
                                                                    x l))))
                                                                   (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ')' ')')
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '#' '#')
                                                                    (Earley_core.Earley.fsequence_position
                                                                    class_path
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun cp ->
                                                                    let _loc_cp
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun tes
                                                                    ->
                                                                    fun te ->
                                                                    Typ.class_
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    cp
                                                                    _loc_cp)
                                                                    (te ::
                                                                    tes))))))))))
                                                        (List.cons
                                                           ((fun
                                                               (allow_par,
                                                                lvl)
                                                               ->
                                                               lvl <=
                                                                 ProdType),
                                                             (Earley_core.Earley.fsequence
                                                                (Earley.list2
                                                                   (typexpr_lvl
                                                                    DashType)
                                                                   (Earley_core.Earley.alternatives
                                                                    (List.cons
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "\195\151"
                                                                    "\195\151")
                                                                    (Earley_core.Earley.empty
                                                                    ()))
                                                                    (List.cons
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '*' '*')
                                                                    (Earley_core.Earley.empty
                                                                    ())) []))))
                                                                (Earley_core.Earley.empty_pos
                                                                   (fun
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
                                                                    fun tes
                                                                    ->
                                                                    Typ.tuple
                                                                    ~loc:_loc
                                                                    tes))))
                                                           [])))))))))))))))))),
      (fun (allow_par, lvl) -> []))
let type_param = Earley_core.Earley.declare_grammar "type_param"
let _ =
  Earley_core.Earley.set_grammar type_param
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence opt_variance
             (Earley_core.Earley.fsequence_position
                (Earley_core.Earley.char '_' '_')
                (Earley_core.Earley.empty
                   (fun str1 ->
                      fun pos1 ->
                        fun str2 ->
                          fun pos2 ->
                            fun j ->
                              let _loc_j = locate str1 pos1 str2 pos2 in
                              fun var -> ((Typ.any ~loc:_loc_j ()), var)))))
          (List.cons
             (Earley_core.Earley.fsequence opt_variance
                (Earley_core.Earley.fsequence_position
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '\'' '\'')
                      (Earley_core.Earley.fsequence ident
                         (Earley_core.Earley.empty
                            (fun _default_0 -> _default_0))))
                   (Earley_core.Earley.empty
                      (fun str1 ->
                         fun pos1 ->
                           fun str2 ->
                             fun pos2 ->
                               fun id ->
                                 let _loc_id = locate str1 pos1 str2 pos2 in
                                 fun var -> ((Typ.var ~loc:_loc_id id), var)))))
             [])))
let type_params = Earley_core.Earley.declare_grammar "type_params"
let _ =
  Earley_core.Earley.set_grammar type_params
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '(' '(')
             (Earley_core.Earley.fsequence type_param
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.apply (fun f -> f [])
                      (Earley_core.Earley.fixpoint' (fun l -> l)
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ',' ',')
                            (Earley_core.Earley.fsequence type_param
                               (Earley_core.Earley.empty (fun tp -> tp))))
                         (fun x -> fun f -> fun l -> f (List.cons x l))))
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char ')' ')')
                      (Earley_core.Earley.empty
                         (fun tps -> fun tp -> tp :: tps))))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.empty ()) (Earley_core.Earley.empty []))
             (List.cons
                (Earley_core.Earley.fsequence type_param
                   (Earley_core.Earley.empty (fun tp -> [tp]))) []))))
let type_equation = Earley_core.Earley.declare_grammar "type_equation"
let _ =
  Earley_core.Earley.set_grammar type_equation
    (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '=' '=')
       (Earley_core.Earley.fsequence private_flag
          (Earley_core.Earley.fsequence typexpr
             (Earley_core.Earley.empty (fun te -> fun p -> (p, te))))))
let type_constraint = Earley_core.Earley.declare_grammar "type_constraint"
let _ =
  Earley_core.Earley.set_grammar type_constraint
    (Earley_core.Earley.fsequence constraint_kw
       (Earley_core.Earley.fsequence_position
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '\'' '\'')
             (Earley_core.Earley.fsequence ident
                (Earley_core.Earley.empty (fun _default_0 -> _default_0))))
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '=' '=')
             (Earley_core.Earley.fsequence typexpr
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun te ->
                              fun str1 ->
                                fun pos1 ->
                                  fun str2 ->
                                    fun pos2 ->
                                      fun id ->
                                        let _loc_id =
                                          locate str1 pos1 str2 pos2 in
                                        fun _default_0 ->
                                          ((Typ.var ~loc:_loc_id id), te,
                                            (merge2 _loc_id _loc))))))))
let constr_name2 = Earley_core.Earley.declare_grammar "constr_name2"
let _ =
  Earley_core.Earley.set_grammar constr_name2
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '(' '(')
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ')' ')')
                (Earley_core.Earley.empty "()"))) (List.cons constr_name [])))
let (bar, bar__set__grammar) = Earley_core.Earley.grammar_family "bar"
let _ =
  bar__set__grammar
    (fun with_bar ->
       Earley_core.Earley.alternatives
         (List.cons
            (Earley_core.Earley.fsequence_ignore
               (Earley_core.Earley.char '|' '|')
               (Earley_core.Earley.empty ()))
            (List.append
               (if not with_bar
                then
                  List.cons
                    (Earley_core.Earley.fsequence_ignore
                       (Earley_core.Earley.empty ())
                       (Earley_core.Earley.empty ())) []
                else []) [])))
let (constr_decl, constr_decl__set__grammar) =
  Earley_core.Earley.grammar_family "constr_decl"
let _ =
  constr_decl__set__grammar
    (fun with_bar ->
       Earley_core.Earley.fsequence (bar with_bar)
         (Earley_core.Earley.fsequence_position constr_name2
            (Earley_core.Earley.fsequence
               (Earley_core.Earley.alternatives
                  (List.cons
                     (Earley_core.Earley.fsequence_ignore
                        (Earley_core.Earley.char ':' ':')
                        (Earley_core.Earley.fsequence_ignore
                           (Earley_core.Earley.char '{' '{')
                           (Earley_core.Earley.fsequence field_decl_list
                              (Earley_core.Earley.fsequence_ignore
                                 (Earley_core.Earley.char '}' '}')
                                 (Earley_core.Earley.fsequence arrow_re
                                    (Earley_core.Earley.fsequence
                                       (typexpr_lvl (next_type_prio Arr))
                                       (Earley_core.Earley.empty
                                          (fun te ->
                                             fun _default_0 ->
                                               fun fds ->
                                                 ((Pcstr_record fds),
                                                   (Some te))))))))))
                     (List.cons
                        (Earley_core.Earley.fsequence
                           (Earley_core.Earley.option None
                              (Earley_core.Earley.apply (fun x -> Some x)
                                 (Earley_core.Earley.fsequence_ignore of_kw
                                    (Earley_core.Earley.fsequence
                                       (Earley_core.Earley.alternatives
                                          (List.cons
                                             (Earley_core.Earley.fsequence
                                                typexpr_nopar
                                                (Earley_core.Earley.empty
                                                   (fun te -> (te, false))))
                                             (List.cons
                                                (Earley_core.Earley.fsequence_ignore
                                                   (Earley_core.Earley.char
                                                      '(' '(')
                                                   (Earley_core.Earley.fsequence
                                                      typexpr
                                                      (Earley_core.Earley.fsequence_ignore
                                                         (Earley_core.Earley.char
                                                            ')' ')')
                                                         (Earley_core.Earley.empty
                                                            (fun te ->
                                                               (te, true))))))
                                                [])))
                                       (Earley_core.Earley.empty
                                          (fun _default_0 -> _default_0))))))
                           (Earley_core.Earley.empty
                              (fun te ->
                                 let tes =
                                   match te with
                                   | None -> []
                                   | Some
                                       ({ ptyp_desc = Ptyp_tuple tes },
                                        false)
                                       -> tes
                                   | Some (t, _) -> [t] in
                                 ((Pcstr_tuple tes), None))))
                        (List.cons
                           (Earley_core.Earley.fsequence of_kw
                              (Earley_core.Earley.fsequence_ignore
                                 (Earley_core.Earley.char '{' '{')
                                 (Earley_core.Earley.fsequence
                                    field_decl_list
                                    (Earley_core.Earley.fsequence_ignore
                                       (Earley_core.Earley.char '}' '}')
                                       (Earley_core.Earley.empty
                                          (fun fds ->
                                             fun _default_0 ->
                                               ((Pcstr_record fds), None)))))))
                           (List.cons
                              (Earley_core.Earley.fsequence_ignore
                                 (Earley_core.Earley.char ':' ':')
                                 (Earley_core.Earley.fsequence
                                    (Earley_core.Earley.option []
                                       (Earley_core.Earley.fsequence
                                          (typexpr_lvl
                                             (next_type_prio ProdType))
                                          (Earley_core.Earley.fsequence
                                             (Earley_core.Earley.apply
                                                (fun f -> f [])
                                                (Earley_core.Earley.fixpoint'
                                                   (fun l -> l)
                                                   (Earley_core.Earley.fsequence_ignore
                                                      (Earley_core.Earley.char
                                                         '*' '*')
                                                      (Earley_core.Earley.fsequence
                                                         (typexpr_lvl
                                                            (next_type_prio
                                                               ProdType))
                                                         (Earley_core.Earley.empty
                                                            (fun _default_0
                                                               -> _default_0))))
                                                   (fun x ->
                                                      fun f ->
                                                        fun l ->
                                                          f (List.cons x l))))
                                             (Earley_core.Earley.fsequence
                                                arrow_re
                                                (Earley_core.Earley.empty
                                                   (fun _default_0 ->
                                                      fun tes ->
                                                        fun te -> te :: tes))))))
                                    (Earley_core.Earley.fsequence
                                       (typexpr_lvl (next_type_prio Arr))
                                       (Earley_core.Earley.empty
                                          (fun te ->
                                             fun tes ->
                                               ((Pcstr_tuple tes), (Some te)))))))
                              [])))))
               (Earley_core.Earley.fsequence post_item_attributes
                  (Earley_core.Earley.empty
                     (fun a ->
                        fun ((args, res) as _default_0) ->
                          fun str1 ->
                            fun pos1 ->
                              fun str2 ->
                                fun pos2 ->
                                  fun cn ->
                                    let _loc_cn = locate str1 pos1 str2 pos2 in
                                    fun _default_1 ->
                                      let name = id_loc cn _loc_cn in
                                      (name, args, res, a)))))))
[@@@ocaml.text " FIXME OCAML: the bar is included in position "]
let (type_constr_decl, type_constr_decl__set__grammar) =
  Earley_core.Earley.grammar_family "type_constr_decl"
let _ =
  type_constr_decl__set__grammar
    (fun with_bar ->
       Earley_core.Earley.fsequence (constr_decl with_bar)
         (Earley_core.Earley.empty_pos
            (fun __loc__start__buf ->
               fun __loc__start__pos ->
                 fun __loc__end__buf ->
                   fun __loc__end__pos ->
                     let _loc =
                       locate __loc__start__buf __loc__start__pos
                         __loc__end__buf __loc__end__pos in
                     fun ((name, args, res, a) as _default_0) ->
                       Type.constructor ~attrs:(attach_attrib _loc a)
                         ~loc:_loc ~args ?res name)))
let (type_constr_extn, type_constr_extn__set__grammar) =
  Earley_core.Earley.grammar_family "type_constr_extn"
let _ =
  type_constr_extn__set__grammar
    (fun with_bar ->
       Earley_core.Earley.alternatives
         (List.cons
            (Earley_core.Earley.fsequence_position lident
               (Earley_core.Earley.fsequence_ignore
                  (Earley_core.Earley.char '=' '=')
                  (Earley_core.Earley.fsequence_position constr
                     (Earley_core.Earley.fsequence post_item_attributes
                        (Earley_core.Earley.empty_pos
                           (fun __loc__start__buf ->
                              fun __loc__start__pos ->
                                fun __loc__end__buf ->
                                  fun __loc__end__pos ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    fun a ->
                                      fun str1 ->
                                        fun pos1 ->
                                          fun str2 ->
                                            fun pos2 ->
                                              fun cn ->
                                                let _loc_cn =
                                                  locate str1 pos1 str2 pos2 in
                                                fun str1 ->
                                                  fun pos1 ->
                                                    fun str2 ->
                                                      fun pos2 ->
                                                        fun li ->
                                                          let _loc_li =
                                                            locate str1 pos1
                                                              str2 pos2 in
                                                          Te.rebind
                                                            ~attrs:(attach_attrib
                                                                    _loc a)
                                                            ~loc:_loc
                                                            (id_loc li
                                                               _loc_li)
                                                            (id_loc cn
                                                               _loc_cn)))))))
            (List.cons
               (Earley_core.Earley.fsequence (constr_decl with_bar)
                  (Earley_core.Earley.empty_pos
                     (fun __loc__start__buf ->
                        fun __loc__start__pos ->
                          fun __loc__end__buf ->
                            fun __loc__end__pos ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              fun ((name, args, res, a) as _default_0) ->
                                Te.decl ~attrs:(attach_attrib _loc a)
                                  ~loc:_loc ~args ?res name))) [])))
let _ =
  set_grammar constr_decl_list
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty []))
          (List.cons
             (Earley_core.Earley.fsequence (type_constr_decl false)
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.apply (fun f -> f [])
                      (Earley_core.Earley.fixpoint' (fun l -> l)
                         (type_constr_decl true)
                         (fun x -> fun f -> fun l -> f (List.cons x l))))
                   (Earley_core.Earley.empty (fun cds -> fun cd -> cd :: cds))))
             [])))
let constr_extn_list = Earley_core.Earley.declare_grammar "constr_extn_list"
let _ =
  Earley_core.Earley.set_grammar constr_extn_list
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty []))
          (List.cons
             (Earley_core.Earley.fsequence (type_constr_extn false)
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.apply (fun f -> f [])
                      (Earley_core.Earley.fixpoint' (fun l -> l)
                         (type_constr_extn true)
                         (fun x -> fun f -> fun l -> f (List.cons x l))))
                   (Earley_core.Earley.empty (fun cds -> fun cd -> cd :: cds))))
             [])))
let field_decl_semi = Earley_core.Earley.declare_grammar "field_decl_semi"
let _ =
  Earley_core.Earley.set_grammar field_decl_semi
    (Earley_core.Earley.fsequence mutable_flag
       (Earley_core.Earley.fsequence_position field_name
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.string ":" ":")
             (Earley_core.Earley.fsequence poly_typexpr
                (Earley_core.Earley.fsequence semi_col
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun _default_0 ->
                                 fun pte ->
                                   fun str1 ->
                                     fun pos1 ->
                                       fun str2 ->
                                         fun pos2 ->
                                           fun fn ->
                                             let _loc_fn =
                                               locate str1 pos1 str2 pos2 in
                                             fun mut ->
                                               Type.field ~loc:_loc
                                                 ~attrs:(attach_attrib _loc
                                                           []) ~mut
                                                 (id_loc fn _loc_fn) pte)))))))
let field_decl = Earley_core.Earley.declare_grammar "field_decl"
let _ =
  Earley_core.Earley.set_grammar field_decl
    (Earley_core.Earley.fsequence mutable_flag
       (Earley_core.Earley.fsequence_position field_name
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.string ":" ":")
             (Earley_core.Earley.fsequence poly_typexpr
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun pte ->
                              fun str1 ->
                                fun pos1 ->
                                  fun str2 ->
                                    fun pos2 ->
                                      fun fn ->
                                        let _loc_fn =
                                          locate str1 pos1 str2 pos2 in
                                        fun mut ->
                                          Type.field ~loc:_loc
                                            ~attrs:(attach_attrib _loc [])
                                            ~mut (id_loc fn _loc_fn) pte))))))
let field_decl_aux = Earley_core.Earley.declare_grammar "field_decl_aux"
let _ =
  Earley_core.Earley.set_grammar field_decl_aux
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence field_decl_aux
             (Earley_core.Earley.fsequence field_decl_semi
                (Earley_core.Earley.empty (fun fd -> fun fs -> fd :: fs))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.empty ()) (Earley_core.Earley.empty []))
             [])))
let _ =
  set_grammar field_decl_list
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence field_decl_aux
             (Earley_core.Earley.fsequence field_decl
                (Earley_core.Earley.empty
                   (fun fd -> fun fs -> List.rev (fd :: fs)))))
          (List.cons
             (Earley_core.Earley.fsequence field_decl_aux
                (Earley_core.Earley.empty (fun fs -> List.rev fs))) [])))
let type_representation =
  Earley_core.Earley.declare_grammar "type_representation"
let _ =
  Earley_core.Earley.set_grammar type_representation
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.string ".." "..")
             (Earley_core.Earley.empty Ptype_open))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "{" "{")
                (Earley_core.Earley.fsequence field_decl_list
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.string "}" "}")
                      (Earley_core.Earley.empty (fun fds -> Ptype_record fds)))))
             (List.cons
                (Earley_core.Earley.fsequence constr_decl_list
                   (Earley_core.Earley.empty
                      (fun cds ->
                         if cds = [] then give_up (); Ptype_variant cds))) []))))
let type_information = Earley_core.Earley.declare_grammar "type_information"
let _ =
  Earley_core.Earley.set_grammar type_information
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x) type_equation))
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.option None
             (Earley_core.Earley.apply (fun x -> Some x)
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '=' '=')
                   (Earley_core.Earley.fsequence private_flag
                      (Earley_core.Earley.fsequence type_representation
                         (Earley_core.Earley.empty
                            (fun tr -> fun pri -> (pri, tr))))))))
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.apply (fun f -> f [])
                (Earley_core.Earley.fixpoint' (fun l -> l) type_constraint
                   (fun x -> fun f -> fun l -> f (List.cons x l))))
             (Earley_core.Earley.empty
                (fun cstrs ->
                   fun ptr ->
                     fun te ->
                       let (pri, tkind) =
                         match ptr with
                         | None -> (Public, Ptype_abstract)
                         | Some c -> c in
                       (pri, te, tkind, cstrs))))))
let typedef_gen att constr filter =
  Earley_core.Earley.fsequence type_params
    (Earley_core.Earley.fsequence_position constr
       (Earley_core.Earley.fsequence type_information
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.alternatives
                (List.append
                   (if not att
                    then
                      List.cons
                        (Earley_core.Earley.fsequence_ignore
                           (Earley_core.Earley.empty ())
                           (Earley_core.Earley.empty [])) []
                    else [])
                   (List.append
                      (if att then List.cons post_item_attributes [] else [])
                      [])))
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun a ->
                           fun ti ->
                             fun str1 ->
                               fun pos1 ->
                                 fun str2 ->
                                   fun pos2 ->
                                     fun tcn ->
                                       let _loc_tcn =
                                         locate str1 pos1 str2 pos2 in
                                       fun params ->
                                         fun prev_loc ->
                                           let _loc =
                                             match prev_loc with
                                             | None -> _loc
                                             | Some l -> merge2 l _loc in
                                           let (pri, te, kind, cstrs) = ti in
                                           let (priv, manifest) =
                                             match te with
                                             | None -> (pri, None)
                                             | Some (Private, te) when
                                                 pri = Private -> give_up ()
                                             | Some (Private, te) ->
                                                 (Private, (Some te))
                                             | Some (_, te) ->
                                                 (pri, (Some te)) in
                                           let ty =
                                             let attrs =
                                               if att
                                               then attach_attrib _loc a
                                               else [] in
                                             let name =
                                               id_loc (filter tcn) _loc_tcn in
                                             Type.mk ~loc:_loc ~attrs ~params
                                               ~cstrs ~kind ~priv ?manifest
                                               name in
                                           ((id_loc tcn _loc_tcn), ty))))))
let type_extension = Earley_core.Earley.declare_grammar "type_extension"
let _ =
  Earley_core.Earley.set_grammar type_extension
    (Earley_core.Earley.fsequence type_kw
       (Earley_core.Earley.fsequence type_params
          (Earley_core.Earley.fsequence_position typeconstr
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "+=" "+=")
                (Earley_core.Earley.fsequence private_flag
                   (Earley_core.Earley.fsequence constr_extn_list
                      (Earley_core.Earley.fsequence post_item_attributes
                         (Earley_core.Earley.empty
                            (fun attrs ->
                               fun cds ->
                                 fun priv ->
                                   fun str1 ->
                                     fun pos1 ->
                                       fun str2 ->
                                         fun pos2 ->
                                           fun tcn ->
                                             let _loc_tcn =
                                               locate str1 pos1 str2 pos2 in
                                             fun params ->
                                               fun _default_0 ->
                                                 let tcn =
                                                   id_loc tcn _loc_tcn in
                                                 Te.mk ~attrs ~params ~priv
                                                   tcn cds)))))))))
let typedef = Earley_core.Earley.declare_grammar "typedef"
let _ =
  Earley_core.Earley.set_grammar typedef
    (typedef_gen true typeconstr_name (fun x -> x))
let typedef_in_constraint =
  Earley_core.Earley.declare_grammar "typedef_in_constraint"
let _ =
  Earley_core.Earley.set_grammar typedef_in_constraint
    (typedef_gen false typeconstr Longident.last)
let type_definition = Earley_core.Earley.declare_grammar "type_definition"
let _ =
  Earley_core.Earley.set_grammar type_definition
    (Earley_core.Earley.fsequence_position type_kw
       (Earley_core.Earley.fsequence typedef
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.apply (fun f -> f [])
                (Earley_core.Earley.fixpoint' (fun l -> l)
                   (Earley_core.Earley.fsequence_position and_kw
                      (Earley_core.Earley.fsequence typedef
                         (Earley_core.Earley.empty
                            (fun td ->
                               fun str1 ->
                                 fun pos1 ->
                                   fun str2 ->
                                     fun pos2 ->
                                       fun l ->
                                         let _loc_l =
                                           locate str1 pos1 str2 pos2 in
                                         snd (td (Some _loc_l))))))
                   (fun x -> fun f -> fun l -> f (List.cons x l))))
             (Earley_core.Earley.empty
                (fun tds ->
                   fun td ->
                     fun str1 ->
                       fun pos1 ->
                         fun str2 ->
                           fun pos2 ->
                             fun l ->
                               let _loc_l = locate str1 pos1 str2 pos2 in
                               (snd (td (Some _loc_l))) :: tds)))))
let exception_definition =
  Earley_core.Earley.declare_grammar "exception_definition"
let _ =
  Earley_core.Earley.set_grammar exception_definition
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence exception_kw
             (Earley_core.Earley.fsequence (constr_decl false)
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun ((name, args, res, a) as _default_0) ->
                              fun _default_1 ->
                                let cd =
                                  Te.decl ~attrs:(attach_attrib _loc a)
                                    ~loc:_loc ~args ?res name in
                                let cd = Te.mk_exception ~loc:_loc cd in
                                Str.exception_ ~loc:_loc cd))))
          (List.cons
             (Earley_core.Earley.fsequence exception_kw
                (Earley_core.Earley.fsequence_position constr_name
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '=' '=')
                      (Earley_core.Earley.fsequence_position constr
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun str1 ->
                                       fun pos1 ->
                                         fun str2 ->
                                           fun pos2 ->
                                             fun c ->
                                               let _loc_c =
                                                 locate str1 pos1 str2 pos2 in
                                               fun str1 ->
                                                 fun pos1 ->
                                                   fun str2 ->
                                                     fun pos2 ->
                                                       fun cn ->
                                                         let _loc_cn =
                                                           locate str1 pos1
                                                             str2 pos2 in
                                                         fun _default_0 ->
                                                           let name =
                                                             id_loc cn
                                                               _loc_cn in
                                                           let ex =
                                                             id_loc c _loc_c in
                                                           let rb =
                                                             Te.rebind
                                                               ~loc:_loc name
                                                               ex in
                                                           let rb =
                                                             Te.mk_exception
                                                               ~loc:_loc rb in
                                                           Str.exception_
                                                             ~loc:_loc rb))))))
             [])))
let class_field_spec = declare_grammar "class_field_spec"
let class_body_type = declare_grammar "class_body_type"
let virt_mut = Earley_core.Earley.declare_grammar "virt_mut"
let _ =
  Earley_core.Earley.set_grammar virt_mut
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence mutable_kw
             (Earley_core.Earley.fsequence virtual_kw
                (Earley_core.Earley.empty
                   (fun _default_0 -> fun _default_1 -> (Virtual, Mutable)))))
          (List.cons
             (Earley_core.Earley.fsequence virtual_flag
                (Earley_core.Earley.fsequence mutable_flag
                   (Earley_core.Earley.empty (fun m -> fun v -> (v, m))))) [])))
let virt_priv = Earley_core.Earley.declare_grammar "virt_priv"
let _ =
  Earley_core.Earley.set_grammar virt_priv
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence private_kw
             (Earley_core.Earley.fsequence virtual_kw
                (Earley_core.Earley.empty
                   (fun _default_0 -> fun _default_1 -> (Virtual, Private)))))
          (List.cons
             (Earley_core.Earley.fsequence virtual_flag
                (Earley_core.Earley.fsequence private_flag
                   (Earley_core.Earley.empty (fun p -> fun v -> (v, p))))) [])))
let _ =
  set_grammar class_field_spec
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence floating_extension
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun ext -> Ctf.extension ~loc:_loc ext)))
          (List.cons
             (Earley_core.Earley.fsequence inherit_kw
                (Earley_core.Earley.fsequence class_body_type
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun cbt ->
                                 fun _default_0 -> Ctf.inherit_ ~loc:_loc cbt))))
             (List.cons
                (Earley_core.Earley.fsequence val_kw
                   (Earley_core.Earley.fsequence virt_mut
                      (Earley_core.Earley.fsequence_position inst_var_name
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ':' ':')
                            (Earley_core.Earley.fsequence typexpr
                               (Earley_core.Earley.empty_pos
                                  (fun __loc__start__buf ->
                                     fun __loc__start__pos ->
                                       fun __loc__end__buf ->
                                         fun __loc__end__pos ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           fun te ->
                                             fun str1 ->
                                               fun pos1 ->
                                                 fun str2 ->
                                                   fun pos2 ->
                                                     fun ivn ->
                                                       let _loc_ivn =
                                                         locate str1 pos1
                                                           str2 pos2 in
                                                       fun
                                                         ((vir, mut) as
                                                            _default_0)
                                                         ->
                                                         fun _default_1 ->
                                                           Ctf.val_ ~loc:_loc
                                                             (id_loc ivn
                                                                _loc_ivn) mut
                                                             vir te)))))))
                (List.cons
                   (Earley_core.Earley.fsequence method_kw
                      (Earley_core.Earley.fsequence virt_priv
                         (Earley_core.Earley.fsequence method_name
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char ':' ':')
                               (Earley_core.Earley.fsequence poly_typexpr
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun te ->
                                                fun mn ->
                                                  fun
                                                    ((v, pri) as _default_0)
                                                    ->
                                                    fun _default_1 ->
                                                      Ctf.method_ ~loc:_loc
                                                        mn pri v te)))))))
                   (List.cons
                      (Earley_core.Earley.fsequence constraint_kw
                         (Earley_core.Earley.fsequence typexpr
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '=' '=')
                               (Earley_core.Earley.fsequence typexpr
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun te' ->
                                                fun te ->
                                                  fun _default_0 ->
                                                    Ctf.constraint_ ~loc:_loc
                                                      te te'))))))
                      (List.cons
                         (Earley_core.Earley.fsequence floating_attribute
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun attr ->
                                          Ctf.attribute ~loc:_loc attr))) [])))))))
let _ =
  set_grammar class_body_type
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.option []
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '[' '[')
                   (Earley_core.Earley.fsequence typexpr
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.apply (fun f -> f [])
                            (Earley_core.Earley.fixpoint' (fun l -> l)
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ',' ',')
                                  (Earley_core.Earley.fsequence typexpr
                                     (Earley_core.Earley.empty (fun te -> te))))
                               (fun x -> fun f -> fun l -> f (List.cons x l))))
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ']' ']')
                            (Earley_core.Earley.empty
                               (fun tes -> fun te -> te :: tes)))))))
             (Earley_core.Earley.fsequence_position classtype_path
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun ctp ->
                                      let _loc_ctp =
                                        locate str1 pos1 str2 pos2 in
                                      fun tes ->
                                        Cty.constr ~loc:_loc
                                          (id_loc ctp _loc_ctp) tes))))
          (List.cons
             (Earley_core.Earley.fsequence object_kw
                (Earley_core.Earley.fsequence_position
                   (Earley_core.Earley.option None
                      (Earley_core.Earley.apply (fun x -> Some x)
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char '(' '(')
                            (Earley_core.Earley.fsequence typexpr
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ')' ')')
                                  (Earley_core.Earley.empty (fun te -> te)))))))
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.apply (fun f -> f [])
                         (Earley_core.Earley.fixpoint' (fun l -> l)
                            class_field_spec
                            (fun x -> fun f -> fun l -> f (List.cons x l))))
                      (Earley_core.Earley.fsequence end_kw
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun _default_0 ->
                                       fun cfs ->
                                         fun str1 ->
                                           fun pos1 ->
                                             fun str2 ->
                                               fun pos2 ->
                                                 fun te ->
                                                   let _loc_te =
                                                     locate str1 pos1 str2
                                                       pos2 in
                                                   fun _default_1 ->
                                                     let self =
                                                       match te with
                                                       | None ->
                                                           Typ.any
                                                             ~loc:_loc_te ()
                                                       | Some t -> t in
                                                     Cty.signature ~loc:_loc
                                                       (Csig.mk self cfs)))))))
             [])))
let class_type = Earley_core.Earley.declare_grammar "class_type"
let _ =
  Earley_core.Earley.set_grammar class_type
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.apply (fun f -> f [])
          (Earley_core.Earley.fixpoint' (fun l -> l)
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.option Nolabel maybe_opt_label)
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ':' ':')
                   (Earley_core.Earley.fsequence typexpr
                      (Earley_core.Earley.empty (fun te -> fun l -> (l, te))))))
             (fun x -> fun f -> fun l -> f (List.cons x l))))
       (Earley_core.Earley.fsequence class_body_type
          (Earley_core.Earley.empty_pos
             (fun __loc__start__buf ->
                fun __loc__start__pos ->
                  fun __loc__end__buf ->
                    fun __loc__end__pos ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      fun cbt ->
                        fun tes ->
                          let app acc (lab, te) =
                            Cty.arrow ~loc:_loc lab te acc in
                          List.fold_left app cbt (List.rev tes)))))
let type_parameters = Earley_core.Earley.declare_grammar "type_parameters"
let _ =
  Earley_core.Earley.set_grammar type_parameters
    (Earley_core.Earley.fsequence type_param
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l)
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "," ",")
                   (Earley_core.Earley.fsequence type_param
                      (Earley_core.Earley.empty (fun i2 -> i2))))
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.empty (fun l -> fun i1 -> i1 :: l))))
let class_spec = Earley_core.Earley.declare_grammar "class_spec"
let _ =
  Earley_core.Earley.set_grammar class_spec
    (Earley_core.Earley.fsequence virtual_flag
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.option []
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "[" "[")
                (Earley_core.Earley.fsequence type_parameters
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.string "]" "]")
                      (Earley_core.Earley.empty (fun params -> params))))))
          (Earley_core.Earley.fsequence_position class_name
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string ":" ":")
                (Earley_core.Earley.fsequence class_type
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun ct ->
                                 fun str1 ->
                                   fun pos1 ->
                                     fun str2 ->
                                       fun pos2 ->
                                         fun cn ->
                                           let _loc_cn =
                                             locate str1 pos1 str2 pos2 in
                                           fun params ->
                                             fun virt ->
                                               Ci.mk ~loc:_loc
                                                 ~attrs:(attach_attrib _loc
                                                           []) ~virt ~params
                                                 (id_loc cn _loc_cn) ct)))))))
let class_specification =
  Earley_core.Earley.declare_grammar "class_specification"
let _ =
  Earley_core.Earley.set_grammar class_specification
    (Earley_core.Earley.fsequence class_kw
       (Earley_core.Earley.fsequence class_spec
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.apply (fun f -> f [])
                (Earley_core.Earley.fixpoint' (fun l -> l)
                   (Earley_core.Earley.fsequence_ignore and_kw
                      (Earley_core.Earley.fsequence class_spec
                         (Earley_core.Earley.empty
                            (fun _default_0 -> _default_0))))
                   (fun x -> fun f -> fun l -> f (List.cons x l))))
             (Earley_core.Earley.empty
                (fun css -> fun cs -> fun _default_0 -> cs :: css)))))
let classtype_def = Earley_core.Earley.declare_grammar "classtype_def"
let _ =
  Earley_core.Earley.set_grammar classtype_def
    (Earley_core.Earley.fsequence virtual_flag
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.option []
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "[" "[")
                (Earley_core.Earley.fsequence type_parameters
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.string "]" "]")
                      (Earley_core.Earley.empty (fun tp -> tp))))))
          (Earley_core.Earley.fsequence_position class_name
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '=' '=')
                (Earley_core.Earley.fsequence class_body_type
                   (Earley_core.Earley.empty
                      (fun cbt ->
                         fun str1 ->
                           fun pos1 ->
                             fun str2 ->
                               fun pos2 ->
                                 fun cn ->
                                   let _loc_cn = locate str1 pos1 str2 pos2 in
                                   fun params ->
                                     fun virt ->
                                       fun loc ->
                                         Ci.mk ~loc
                                           ~attrs:(attach_attrib loc [])
                                           ~virt ~params (id_loc cn _loc_cn)
                                           cbt)))))))
let classtype_definition =
  Earley_core.Earley.declare_grammar "classtype_definition"
let _ =
  Earley_core.Earley.set_grammar classtype_definition
    (Earley_core.Earley.fsequence_position class_kw
       (Earley_core.Earley.fsequence type_kw
          (Earley_core.Earley.fsequence_position classtype_def
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.apply (fun f -> f [])
                   (Earley_core.Earley.fixpoint' (fun l -> l)
                      (Earley_core.Earley.fsequence_ignore and_kw
                         (Earley_core.Earley.fsequence classtype_def
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun cd -> cd _loc))))
                      (fun x -> fun f -> fun l -> f (List.cons x l))))
                (Earley_core.Earley.empty
                   (fun cds ->
                      fun str1 ->
                        fun pos1 ->
                          fun str2 ->
                            fun pos2 ->
                              fun cd ->
                                let _loc_cd = locate str1 pos1 str2 pos2 in
                                fun _default_0 ->
                                  fun str1 ->
                                    fun pos1 ->
                                      fun str2 ->
                                        fun pos2 ->
                                          fun k ->
                                            let _loc_k =
                                              locate str1 pos1 str2 pos2 in
                                            (cd (merge2 _loc_k _loc_cd)) ::
                                              cds))))))
let constant = Earley_core.Earley.declare_grammar "constant"
let _ =
  Earley_core.Earley.set_grammar constant
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence int_litteral
             (Earley_core.Earley.empty
                (fun ((i, suffix) as _default_0) -> Const.integer ?suffix i)))
          (List.cons
             (Earley_core.Earley.fsequence float_litteral
                (Earley_core.Earley.empty
                   (fun ((f, suffix) as _default_0) -> Const.float ?suffix f)))
             (List.cons
                (Earley_core.Earley.fsequence char_litteral
                   (Earley_core.Earley.empty (fun c -> Const.char c)))
                (List.cons
                   (Earley_core.Earley.fsequence string_litteral
                      (Earley_core.Earley.empty
                         (fun ((s, quotation_delimiter) as _default_0) ->
                            Const.string ?quotation_delimiter s)))
                   (List.cons
                      (Earley_core.Earley.fsequence regexp_litteral
                         (Earley_core.Earley.empty (fun s -> Const.string s)))
                      (List.cons
                         (Earley_core.Earley.fsequence new_regexp_litteral
                            (Earley_core.Earley.empty
                               (fun s -> Const.string s))) [])))))))
let neg_constant = Earley_core.Earley.declare_grammar "neg_constant"
let _ =
  Earley_core.Earley.set_grammar neg_constant
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '-' '-')
             (Earley_core.Earley.fsequence int_litteral
                (Earley_core.Earley.empty
                   (fun ((i, suffix) as _default_0) ->
                      Const.integer ?suffix ("-" ^ i)))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '-' '-')
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.no_blank_test ())
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x)
                            (Earley_core.Earley.char '.' '.')))
                      (Earley_core.Earley.fsequence float_litteral
                         (Earley_core.Earley.empty
                            (fun ((f, suffix) as _default_0) ->
                               fun _default_1 ->
                                 Const.float ?suffix ("-" ^ f))))))) [])))
let _ =
  set_pattern_lvl
    ((List.cons
        ((fun (as_ok, lvl) -> lvl <= ConsPat),
          (Earley_core.Earley.fsequence
             (pattern_lvl (true, (next_pat_prio ConsPat)))
             (Earley_core.Earley.fsequence_position
                (Earley_core.Earley.string "::" "::")
                (Earley_core.Earley.fsequence (pattern_lvl (false, ConsPat))
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun p' ->
                                 fun str1 ->
                                   fun pos1 ->
                                     fun str2 ->
                                       fun pos2 ->
                                         fun c ->
                                           let _loc_c =
                                             locate str1 pos1 str2 pos2 in
                                           fun p ->
                                             let cons =
                                               id_loc (Lident "::") _loc_c in
                                             let args =
                                               Pat.tuple ~loc:(ghost _loc)
                                                 [p; p'] in
                                             Pat.construct ~loc:_loc cons
                                               (Some args)))))))
        (List.cons
           ((fun _ -> true),
             (Earley_core.Earley.fsequence_position value_name
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun vn ->
                                      let _loc_vn =
                                        locate str1 pos1 str2 pos2 in
                                      Pat.var ~loc:_loc (id_loc vn _loc_vn)))))
           (List.cons
              ((fun _ -> true),
                (Earley_core.Earley.fsequence joker_kw
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun _default_0 -> Pat.any ~loc:_loc ()))))
              (List.cons
                 ((fun _ -> true),
                   (Earley_core.Earley.fsequence char_litteral
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.string ".." "..")
                         (Earley_core.Earley.fsequence char_litteral
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun c2 ->
                                          fun c1 ->
                                            Pat.interval ~loc:_loc
                                              (Const.char c1) (Const.char c2)))))))
                 (List.cons
                    ((fun (as_ok, lvl) -> lvl <= AtomPat),
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.alternatives
                            (List.cons neg_constant (List.cons constant [])))
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun c -> Pat.constant ~loc:_loc c))))
                    (List.cons
                       ((fun _ -> true),
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char '(' '(')
                            (Earley_core.Earley.fsequence pattern
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.option None
                                     (Earley_core.Earley.apply
                                        (fun x -> Some x)
                                        (Earley_core.Earley.fsequence_ignore
                                           (Earley_core.Earley.char ':' ':')
                                           (Earley_core.Earley.fsequence
                                              typexpr
                                              (Earley_core.Earley.empty
                                                 (fun _default_0 ->
                                                    _default_0))))))
                                  (Earley_core.Earley.fsequence_ignore
                                     (Earley_core.Earley.char ')' ')')
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun ty ->
                                                   fun p ->
                                                     match ty with
                                                     | None ->
                                                         Pat.mk ~loc:_loc
                                                           p.ppat_desc
                                                     | Some ty ->
                                                         Pat.constraint_
                                                           ~loc:_loc p ty)))))))
                       (List.cons
                          ((fun (as_ok, lvl) -> lvl <= ConstrPat),
                            (Earley_core.Earley.fsequence lazy_kw
                               (Earley_core.Earley.fsequence
                                  (pattern_lvl (false, ConstrPat))
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun p ->
                                                fun _default_0 ->
                                                  Pat.lazy_ ~loc:_loc p)))))
                          (List.cons
                             ((fun (as_ok, lvl) -> lvl <= ConstrPat),
                               (Earley_core.Earley.fsequence exception_kw
                                  (Earley_core.Earley.fsequence
                                     (pattern_lvl (false, ConstrPat))
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun p ->
                                                   fun _default_0 ->
                                                     Pat.exception_ ~loc:_loc
                                                       p)))))
                             (List.cons
                                ((fun (as_ok, lvl) -> lvl <= ConstrPat),
                                  (Earley_core.Earley.fsequence_position
                                     constr
                                     (Earley_core.Earley.fsequence
                                        (pattern_lvl (false, ConstrPat))
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun p ->
                                                      fun str1 ->
                                                        fun pos1 ->
                                                          fun str2 ->
                                                            fun pos2 ->
                                                              fun c ->
                                                                let _loc_c =
                                                                  locate str1
                                                                    pos1 str2
                                                                    pos2 in
                                                                Pat.construct
                                                                  ~loc:_loc
                                                                  (id_loc c
                                                                    _loc_c)
                                                                  (Some p))))))
                                (List.cons
                                   ((fun _ -> true),
                                     (Earley_core.Earley.fsequence_position
                                        constr
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun str1 ->
                                                      fun pos1 ->
                                                        fun str2 ->
                                                          fun pos2 ->
                                                            fun c ->
                                                              let _loc_c =
                                                                locate str1
                                                                  pos1 str2
                                                                  pos2 in
                                                              Pat.construct
                                                                ~loc:_loc
                                                                (id_loc c
                                                                   _loc_c)
                                                                None))))
                                   (List.cons
                                      ((fun _ -> true),
                                        (Earley_core.Earley.fsequence
                                           bool_lit
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun b ->
                                                         Pat.construct
                                                           ~loc:_loc
                                                           (id_loc (Lident b)
                                                              _loc) None))))
                                      (List.cons
                                         ((fun (as_ok, lvl) ->
                                             lvl <= ConstrPat),
                                           (Earley_core.Earley.fsequence
                                              tag_name
                                              (Earley_core.Earley.fsequence
                                                 (pattern_lvl
                                                    (false, ConstrPat))
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
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
                                                             fun p ->
                                                               fun c ->
                                                                 Pat.variant
                                                                   ~loc:_loc
                                                                   c (
                                                                   Some p))))))
                                         (List.cons
                                            ((fun _ -> true),
                                              (Earley_core.Earley.fsequence
                                                 tag_name
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
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
                                                             fun c ->
                                                               Pat.variant
                                                                 ~loc:_loc c
                                                                 None))))
                                            (List.cons
                                               ((fun _ -> true),
                                                 (Earley_core.Earley.fsequence
                                                    (Earley_core.Earley.char
                                                       '#' '#')
                                                    (Earley_core.Earley.fsequence_position
                                                       typeconstr
                                                       (Earley_core.Earley.empty_pos
                                                          (fun
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
                                                                   fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun t ->
                                                                    let _loc_t
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun s ->
                                                                    Pat.type_
                                                                    ~loc:_loc
                                                                    (id_loc t
                                                                    _loc_t))))))
                                               (List.cons
                                                  ((fun _ -> true),
                                                    (Earley_core.Earley.fsequence
                                                       (Earley_core.Earley.char
                                                          '{' '{')
                                                       (Earley_core.Earley.fsequence_position
                                                          field
                                                          (Earley_core.Earley.fsequence
                                                             (Earley_core.Earley.option
                                                                None
                                                                (Earley_core.Earley.apply
                                                                   (fun x ->
                                                                    Some x)
                                                                   (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '=' '=')
                                                                    (Earley_core.Earley.fsequence
                                                                    pattern
                                                                    (Earley_core.Earley.empty
                                                                    (fun p ->
                                                                    p))))))
                                                             (Earley_core.Earley.fsequence
                                                                (Earley_core.Earley.apply
                                                                   (fun f ->
                                                                    f [])
                                                                   (Earley_core.Earley.fixpoint'
                                                                    (fun l ->
                                                                    l)
                                                                    (Earley_core.Earley.fsequence
                                                                    semi_col
                                                                    (Earley_core.Earley.fsequence_position
                                                                    field
                                                                    (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '=' '=')
                                                                    (Earley_core.Earley.fsequence
                                                                    pattern
                                                                    (Earley_core.Earley.empty
                                                                    (fun p ->
                                                                    p))))))
                                                                    (Earley_core.Earley.empty
                                                                    (fun p ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun f ->
                                                                    let _loc_f
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    ((id_loc
                                                                    f _loc_f),
                                                                    p))))))
                                                                    (fun x ->
                                                                    fun f ->
                                                                    fun l ->
                                                                    f
                                                                    (List.cons
                                                                    x l))))
                                                                (Earley_core.Earley.fsequence
                                                                   (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    (Earley_core.Earley.fsequence
                                                                    semi_col
                                                                    (Earley_core.Earley.fsequence
                                                                    joker_kw
                                                                    (Earley_core.Earley.empty
                                                                    (fun
                                                                    _default_0
                                                                    ->
                                                                    fun
                                                                    _default_1
                                                                    -> ()))))))
                                                                   (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    semi_col))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '}' '}')
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun clsd
                                                                    ->
                                                                    fun fps
                                                                    ->
                                                                    fun p ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun f ->
                                                                    let _loc_f
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun s ->
                                                                    let all =
                                                                    ((id_loc
                                                                    f _loc_f),
                                                                    p) :: fps in
                                                                    let f
                                                                    (lab,
                                                                    pat) =
                                                                    match pat
                                                                    with
                                                                    | 
                                                                    Some p ->
                                                                    (lab, p)
                                                                    | 
                                                                    None ->
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
                                                                    (Pat.var
                                                                    ~loc:(
                                                                    lab.loc)
                                                                    slab)) in
                                                                    let all =
                                                                    List.map
                                                                    f all in
                                                                    let cl =
                                                                    match clsd
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    Closed
                                                                    | 
                                                                    Some _ ->
                                                                    Open in
                                                                    Pat.record
                                                                    ~loc:_loc
                                                                    all cl))))))))))
                                                  (List.cons
                                                     ((fun _ -> true),
                                                       (Earley_core.Earley.fsequence_ignore
                                                          (Earley_core.Earley.char
                                                             '[' '[')
                                                          (Earley_core.Earley.fsequence
                                                             (list1 pattern
                                                                semi_col)
                                                             (Earley_core.Earley.fsequence
                                                                (Earley_core.Earley.option
                                                                   None
                                                                   (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    semi_col))
                                                                (Earley_core.Earley.fsequence_position
                                                                   (Earley_core.Earley.char
                                                                    ']' ']')
                                                                   (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun c ->
                                                                    let _loc_c
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun ps ->
                                                                    let nil =
                                                                    id_loc
                                                                    (Lident
                                                                    "[]")
                                                                    (ghost
                                                                    _loc_c) in
                                                                    let hd =
                                                                    match ps
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    assert
                                                                    false
                                                                    | 
                                                                    x::_ -> x in
                                                                    let cons
                                                                    x xs =
                                                                    let cloc
                                                                    =
                                                                    ghost
                                                                    (merge2
                                                                    x.ppat_loc
                                                                    _loc) in
                                                                    let c =
                                                                    id_loc
                                                                    (Lident
                                                                    "::")
                                                                    cloc in
                                                                    let loc =
                                                                    if
                                                                    x == hd
                                                                    then _loc
                                                                    else cloc in
                                                                    Pat.construct
                                                                    ~loc c
                                                                    (Some
                                                                    (Pat.tuple
                                                                    ~loc:cloc
                                                                    [x; xs])) in
                                                                    List.fold_right
                                                                    cons ps
                                                                    (Pat.construct
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc_c)
                                                                    nil None))))))))
                                                     (List.cons
                                                        ((fun _ -> true),
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.char
                                                                '[' '[')
                                                             (Earley_core.Earley.fsequence_ignore
                                                                (Earley_core.Earley.char
                                                                   ']' ']')
                                                                (Earley_core.Earley.empty_pos
                                                                   (fun
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
                                                                    Pat.construct
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    (Lident
                                                                    "[]")
                                                                    _loc)
                                                                    None)))))
                                                        (List.cons
                                                           ((fun _ -> true),
                                                             (Earley_core.Earley.fsequence_ignore
                                                                (Earley_core.Earley.string
                                                                   "[|" "[|")
                                                                (Earley_core.Earley.fsequence
                                                                   (list0
                                                                    pattern
                                                                    semi_col)
                                                                   (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    semi_col))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "|]" "|]")
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun ps ->
                                                                    Pat.array
                                                                    ~loc:_loc
                                                                    ps)))))))
                                                           (List.cons
                                                              ((fun _ -> true),
                                                                (Earley_core.Earley.fsequence_ignore
                                                                   (Earley_core.Earley.char
                                                                    '(' '(')
                                                                   (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ')' ')')
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    Pat.construct
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    (Lident
                                                                    "()")
                                                                    _loc)
                                                                    None)))))
                                                              (List.cons
                                                                 ((fun _ ->
                                                                    true),
                                                                   (Earley_core.Earley.fsequence
                                                                    begin_kw
                                                                    (Earley_core.Earley.fsequence
                                                                    end_kw
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    Pat.construct
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    (Lident
                                                                    "()")
                                                                    _loc)
                                                                    None)))))
                                                                 (List.cons
                                                                    ((fun
                                                                    (as_ok,
                                                                    lvl) ->
                                                                    lvl <=
                                                                    AtomPat),
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '(' '(')
                                                                    (Earley_core.Earley.fsequence
                                                                    module_kw
                                                                    (Earley_core.Earley.fsequence
                                                                    module_name
                                                                    (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ':' ':')
                                                                    (Earley_core.Earley.fsequence
                                                                    package_type
                                                                    (Earley_core.Earley.empty
                                                                    (fun pt
                                                                    -> pt))))))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ')' ')')
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun pt ->
                                                                    fun mn ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let pat =
                                                                    Pat.unpack
                                                                    ~loc:_loc
                                                                    mn in
                                                                    match pt
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    pat
                                                                    | 
                                                                    Some pt
                                                                    ->
                                                                    let pt =
                                                                    Typ.mk
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc)
                                                                    pt.ptyp_desc in
                                                                    Pat.constraint_
                                                                    ~loc:_loc
                                                                    pat pt))))))))
                                                                    (
                                                                    List.cons
                                                                    ((fun
                                                                    (as_ok,
                                                                    lvl) ->
                                                                    lvl <=
                                                                    AltPat),
                                                                    (Earley_core.Earley.fsequence
                                                                    (pattern_lvl
                                                                    (true,
                                                                    AltPat))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '|' '|')
                                                                    (Earley_core.Earley.fsequence
                                                                    (pattern_lvl
                                                                    (false,
                                                                    (next_pat_prio
                                                                    AltPat)))
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun p' ->
                                                                    fun p ->
                                                                    Pat.or_
                                                                    ~loc:_loc
                                                                    p p'))))))
                                                                    (List.cons
                                                                    ((fun
                                                                    (as_ok,
                                                                    lvl) ->
                                                                    lvl <=
                                                                    TupPat),
                                                                    (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.apply
                                                                    (fun f ->
                                                                    f [])
                                                                    (Earley_core.Earley.fixpoint1'
                                                                    (fun l ->
                                                                    l)
                                                                    (Earley_core.Earley.fsequence
                                                                    (pattern_lvl
                                                                    (true,
                                                                    (next_pat_prio
                                                                    TupPat)))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ',' ',')
                                                                    (Earley_core.Earley.empty
                                                                    (fun
                                                                    _default_0
                                                                    ->
                                                                    _default_0))))
                                                                    (fun x ->
                                                                    fun f ->
                                                                    fun l ->
                                                                    f
                                                                    (List.cons
                                                                    x l))))
                                                                    (Earley_core.Earley.fsequence
                                                                    (pattern_lvl
                                                                    (false,
                                                                    (next_pat_prio
                                                                    TupPat)))
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun p ->
                                                                    fun ps ->
                                                                    Pat.tuple
                                                                    ~loc:_loc
                                                                    (ps @ [p]))))))
                                                                    []))))))))))))))))))))))),
      (fun (as_ok, lvl) ->
         List.append
           (if as_ok
            then
              List.cons
                (Earley_core.Earley.fsequence (pattern_lvl (as_ok, lvl))
                   (Earley_core.Earley.fsequence as_kw
                      (Earley_core.Earley.fsequence_position value_name
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun str1 ->
                                       fun pos1 ->
                                         fun str2 ->
                                           fun pos2 ->
                                             fun vn ->
                                               let _loc_vn =
                                                 locate str1 pos1 str2 pos2 in
                                               fun _default_0 ->
                                                 fun p ->
                                                   Pat.alias ~loc:_loc p
                                                     (id_loc vn _loc_vn))))))
                []
            else []) []))
let let_re = "\\(let\\)\\|\\(val\\)\\b"
type assoc =
  | NoAssoc 
  | Left 
  | Right 
let assoc =
  function
  | Prefix|Dot|Dash|Opp -> NoAssoc
  | Prod|Sum|Eq -> Left
  | _ -> Right
let infix_prio s =
  match s.[0] with
  | '*' -> if ((String.length s) > 1) && ((s.[1]) = '*') then Pow else Prod
  | '/'|'%' -> Prod
  | '+'|'-' -> Sum
  | ':' -> if ((String.length s) > 1) && ((s.[1]) = '=') then Aff else Cons
  | '<' -> if ((String.length s) > 1) && ((s.[1]) = '-') then Aff else Eq
  | '@'|'^' -> Append
  | '&' ->
      if
        ((String.length s) = 1) ||
          (((String.length s) = 2) && ((s.[1]) = '&'))
      then Conj
      else Eq
  | '|' -> if ((String.length s) = 2) && ((s.[1]) = '|') then Disj else Eq
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
  Exp.ident ~loc (id_loc (Ldot ((Lident str), name)) loc)
let bigarray_function loc str name =
  Exp.ident ~loc
    (id_loc (Ldot ((Ldot ((Lident "Bigarray"), str)), name)) loc)
let untuplify exp =
  match exp.pexp_desc with | Pexp_tuple es -> es | _ -> [exp]
let bigarray_get loc arr arg =
  let apply fn args =
    let fn = Exp.ident (Location.mknoloc (Longident.parse fn)) in
    Exp.apply ~loc fn (List.map (fun e -> (Nolabel, e)) args) in
  match untuplify arg with
  | c1::[] -> apply "Bigarray.Array1.get" [arr; c1]
  | c1::c2::[] -> apply "Bigarray.Array2.get" [arr; c1; c2]
  | c1::c2::c3::[] -> apply "Bigarray.Array3.get" [arr; c1; c2; c3]
  | cs -> apply "Bigarray.Genarray.get" [arr; Exp.array cs]
let bigarray_set loc arr arg v =
  let apply fn args =
    let fn = Exp.ident (Location.mknoloc (Longident.parse fn)) in
    Exp.apply ~loc fn (List.map (fun e -> (Nolabel, e)) args) in
  match untuplify arg with
  | c1::[] -> apply "Bigarray.Array1.set" [arr; c1; v]
  | c1::c2::[] -> apply "Bigarray.Array2.set" [arr; c1; c2; v]
  | c1::c2::c3::[] -> apply "Bigarray.Array3.set" [arr; c1; c2; c3; v]
  | cs -> apply "Bigarray.Genarray.set" [arr; Exp.array cs; v]
let constructor = Earley_core.Earley.declare_grammar "constructor"
let _ =
  Earley_core.Earley.set_grammar constructor
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "." ".")
                   (Earley_core.Earley.empty (fun m -> m))))))
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.alternatives
             (List.cons bool_lit (List.cons uident [])))
          (Earley_core.Earley.empty
             (fun id ->
                fun m ->
                  match m with | None -> Lident id | Some m -> Ldot (m, id)))))
let argument = Earley_core.Earley.declare_grammar "argument"
let _ =
  Earley_core.Earley.set_grammar argument
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence
             (expression_lvl (NoMatch, (next_exp App)))
             (Earley_core.Earley.empty (fun e -> (Nolabel, e))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '~' '~')
                (Earley_core.Earley.fsequence_position lident
                   (Earley_core.Earley.fsequence no_colon
                      (Earley_core.Earley.empty
                         (fun _default_0 ->
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun id ->
                                      let _loc_id =
                                        locate str1 pos1 str2 pos2 in
                                      ((Labelled id),
                                        (Exp.ident ~loc:_loc_id
                                           (id_loc (Lident id) _loc_id))))))))
             (List.cons
                (Earley_core.Earley.fsequence ty_label
                   (Earley_core.Earley.fsequence
                      (expression_lvl (NoMatch, (next_exp App)))
                      (Earley_core.Earley.empty (fun e -> fun id -> (id, e)))))
                (List.cons
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '?' '?')
                      (Earley_core.Earley.fsequence_position lident
                         (Earley_core.Earley.empty
                            (fun str1 ->
                               fun pos1 ->
                                 fun str2 ->
                                   fun pos2 ->
                                     fun id ->
                                       let _loc_id =
                                         locate str1 pos1 str2 pos2 in
                                       ((Optional id),
                                         (Exp.ident ~loc:_loc_id
                                            (id_loc (Lident id) _loc_id)))))))
                   (List.cons
                      (Earley_core.Earley.fsequence ty_opt_label
                         (Earley_core.Earley.fsequence
                            (expression_lvl (NoMatch, (next_exp App)))
                            (Earley_core.Earley.empty
                               (fun e -> fun id -> (id, e))))) []))))))
let _ =
  set_parameter
    (fun allow_new_type ->
       Earley_core.Earley.alternatives
         (List.append
            (if allow_new_type
             then
               List.cons
                 (Earley_core.Earley.fsequence_ignore
                    (Earley_core.Earley.char '(' '(')
                    (Earley_core.Earley.fsequence type_kw
                       (Earley_core.Earley.fsequence_position typeconstr_name
                          (Earley_core.Earley.fsequence_ignore
                             (Earley_core.Earley.char ')' ')')
                             (Earley_core.Earley.empty
                                (fun str1 ->
                                   fun pos1 ->
                                     fun str2 ->
                                       fun pos2 ->
                                         fun name ->
                                           let _loc_name =
                                             locate str1 pos1 str2 pos2 in
                                           fun _default_0 ->
                                             let name = id_loc name _loc_name in
                                             `Type name)))))) []
             else [])
            (List.cons
               (Earley_core.Earley.fsequence (pattern_lvl (false, AtomPat))
                  (Earley_core.Earley.empty
                     (fun pat -> `Arg (Nolabel, None, pat))))
               (List.cons
                  (Earley_core.Earley.fsequence_ignore
                     (Earley_core.Earley.char '~' '~')
                     (Earley_core.Earley.fsequence_ignore
                        (Earley_core.Earley.char '(' '(')
                        (Earley_core.Earley.fsequence_position lident
                           (Earley_core.Earley.fsequence
                              (Earley_core.Earley.option None
                                 (Earley_core.Earley.apply (fun x -> Some x)
                                    (Earley_core.Earley.fsequence_ignore
                                       (Earley_core.Earley.string ":" ":")
                                       (Earley_core.Earley.fsequence typexpr
                                          (Earley_core.Earley.empty
                                             (fun t -> t))))))
                              (Earley_core.Earley.fsequence_ignore
                                 (Earley_core.Earley.string ")" ")")
                                 (Earley_core.Earley.empty_pos
                                    (fun __loc__start__buf ->
                                       fun __loc__start__pos ->
                                         fun __loc__end__buf ->
                                           fun __loc__end__pos ->
                                             let _loc =
                                               locate __loc__start__buf
                                                 __loc__start__pos
                                                 __loc__end__buf
                                                 __loc__end__pos in
                                             fun t ->
                                               fun str1 ->
                                                 fun pos1 ->
                                                   fun str2 ->
                                                     fun pos2 ->
                                                       fun id ->
                                                         let _loc_id =
                                                           locate str1 pos1
                                                             str2 pos2 in
                                                         let pat =
                                                           Pat.var
                                                             ~loc:_loc_id
                                                             (id_loc id
                                                                _loc_id) in
                                                         let pat =
                                                           match t with
                                                           | None -> pat
                                                           | Some t ->
                                                               Pat.constraint_
                                                                 ~loc:_loc
                                                                 pat t in
                                                         `Arg
                                                           ((Labelled id),
                                                             None, pat))))))))
                  (List.cons
                     (Earley_core.Earley.fsequence ty_label
                        (Earley_core.Earley.fsequence pattern
                           (Earley_core.Earley.empty
                              (fun pat -> fun id -> `Arg (id, None, pat)))))
                     (List.cons
                        (Earley_core.Earley.fsequence_ignore
                           (Earley_core.Earley.char '~' '~')
                           (Earley_core.Earley.fsequence_position lident
                              (Earley_core.Earley.fsequence no_colon
                                 (Earley_core.Earley.empty
                                    (fun _default_0 ->
                                       fun str1 ->
                                         fun pos1 ->
                                           fun str2 ->
                                             fun pos2 ->
                                               fun id ->
                                                 let _loc_id =
                                                   locate str1 pos1 str2 pos2 in
                                                 `Arg
                                                   ((Labelled id), None,
                                                     (Pat.var ~loc:_loc_id
                                                        (id_loc id _loc_id))))))))
                        (List.cons
                           (Earley_core.Earley.fsequence_ignore
                              (Earley_core.Earley.char '?' '?')
                              (Earley_core.Earley.fsequence_ignore
                                 (Earley_core.Earley.char '(' '(')
                                 (Earley_core.Earley.fsequence_position
                                    lident
                                    (Earley_core.Earley.fsequence_position
                                       (Earley_core.Earley.option None
                                          (Earley_core.Earley.apply
                                             (fun x -> Some x)
                                             (Earley_core.Earley.fsequence_ignore
                                                (Earley_core.Earley.char ':'
                                                   ':')
                                                (Earley_core.Earley.fsequence
                                                   typexpr
                                                   (Earley_core.Earley.empty
                                                      (fun t -> t))))))
                                       (Earley_core.Earley.fsequence
                                          (Earley_core.Earley.option None
                                             (Earley_core.Earley.apply
                                                (fun x -> Some x)
                                                (Earley_core.Earley.fsequence_ignore
                                                   (Earley_core.Earley.char
                                                      '=' '=')
                                                   (Earley_core.Earley.fsequence
                                                      expression
                                                      (Earley_core.Earley.empty
                                                         (fun e -> e))))))
                                          (Earley_core.Earley.fsequence_ignore
                                             (Earley_core.Earley.char ')' ')')
                                             (Earley_core.Earley.empty
                                                (fun e ->
                                                   fun str1 ->
                                                     fun pos1 ->
                                                       fun str2 ->
                                                         fun pos2 ->
                                                           fun t ->
                                                             let _loc_t =
                                                               locate str1
                                                                 pos1 str2
                                                                 pos2 in
                                                             fun str1 ->
                                                               fun pos1 ->
                                                                 fun str2 ->
                                                                   fun pos2
                                                                    ->
                                                                    fun id ->
                                                                    let _loc_id
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    let pat =
                                                                    Pat.var
                                                                    ~loc:_loc_id
                                                                    (id_loc
                                                                    id
                                                                    _loc_id) in
                                                                    let pat =
                                                                    match t
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    pat
                                                                    | 
                                                                    Some t ->
                                                                    Pat.constraint_
                                                                    ~loc:(
                                                                    merge2
                                                                    _loc_id
                                                                    _loc_t)
                                                                    pat t in
                                                                    `Arg
                                                                    ((Optional
                                                                    id), e,
                                                                    pat)))))))))
                           (List.cons
                              (Earley_core.Earley.fsequence ty_opt_label
                                 (Earley_core.Earley.fsequence_ignore
                                    (Earley_core.Earley.string "(" "(")
                                    (Earley_core.Earley.fsequence_position
                                       pattern
                                       (Earley_core.Earley.fsequence_position
                                          (Earley_core.Earley.option None
                                             (Earley_core.Earley.apply
                                                (fun x -> Some x)
                                                (Earley_core.Earley.fsequence_ignore
                                                   (Earley_core.Earley.char
                                                      ':' ':')
                                                   (Earley_core.Earley.fsequence
                                                      typexpr
                                                      (Earley_core.Earley.empty
                                                         (fun t -> t))))))
                                          (Earley_core.Earley.fsequence
                                             (Earley_core.Earley.option None
                                                (Earley_core.Earley.apply
                                                   (fun x -> Some x)
                                                   (Earley_core.Earley.fsequence_ignore
                                                      (Earley_core.Earley.char
                                                         '=' '=')
                                                      (Earley_core.Earley.fsequence
                                                         expression
                                                         (Earley_core.Earley.empty
                                                            (fun e -> e))))))
                                             (Earley_core.Earley.fsequence_ignore
                                                (Earley_core.Earley.char ')'
                                                   ')')
                                                (Earley_core.Earley.empty
                                                   (fun e ->
                                                      fun str1 ->
                                                        fun pos1 ->
                                                          fun str2 ->
                                                            fun pos2 ->
                                                              fun t ->
                                                                let _loc_t =
                                                                  locate str1
                                                                    pos1 str2
                                                                    pos2 in
                                                                fun str1 ->
                                                                  fun pos1 ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun pat
                                                                    ->
                                                                    let _loc_pat
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun id ->
                                                                    let pat =
                                                                    match t
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    pat
                                                                    | 
                                                                    Some t ->
                                                                    Pat.constraint_
                                                                    ~loc:(
                                                                    merge2
                                                                    _loc_pat
                                                                    _loc_t)
                                                                    pat t in
                                                                    `Arg
                                                                    (id, e,
                                                                    pat)))))))))
                              (List.cons
                                 (Earley_core.Earley.fsequence ty_opt_label
                                    (Earley_core.Earley.fsequence pattern
                                       (Earley_core.Earley.empty
                                          (fun pat ->
                                             fun id -> `Arg (id, None, pat)))))
                                 (List.cons
                                    (Earley_core.Earley.fsequence_ignore
                                       (Earley_core.Earley.char '?' '?')
                                       (Earley_core.Earley.fsequence_position
                                          lident
                                          (Earley_core.Earley.empty
                                             (fun str1 ->
                                                fun pos1 ->
                                                  fun str2 ->
                                                    fun pos2 ->
                                                      fun id ->
                                                        let _loc_id =
                                                          locate str1 pos1
                                                            str2 pos2 in
                                                        `Arg
                                                          ((Optional id),
                                                            None,
                                                            (Pat.var
                                                               ~loc:_loc_id
                                                               (id_loc id
                                                                  _loc_id)))))))
                                    []))))))))))
let apply_params ?(gh= false)  _loc params e =
  let f acc =
    function
    | (`Arg (lbl, opt, pat), _loc') ->
        Exp.fun_ ~loc:(ghost (merge2 _loc' _loc)) lbl opt pat acc
    | (`Type name, _loc') -> Exp.newtype ~loc:(merge2 _loc' _loc) name acc in
  let e = List.fold_left f e (List.rev params) in
  if gh then e else de_ghost e
[@@@ocaml.text
  " FIXME OCAML: should be ghost, or above should not be ghost "]
let apply_params_cls ?(gh= false)  _loc params e =
  let ghost _loc' = if gh then merge2 _loc' _loc else _loc in
  let f acc =
    function
    | (`Arg (lbl, opt, pat), _loc') ->
        Cl.fun_ ~loc:(ghost _loc') lbl opt pat acc
    | (`Type name, _) -> assert false in
  List.fold_left f e (List.rev params)
[@@@ocaml.text " FIXME OCAML: shoud be ghost as above ? "]
let right_member = Earley_core.Earley.declare_grammar "right_member"
let _ =
  Earley_core.Earley.set_grammar right_member
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.apply (fun f -> f [])
          (Earley_core.Earley.fixpoint1' (fun l -> l)
             (Earley_core.Earley.fsequence_position (parameter true)
                (Earley_core.Earley.empty
                   (fun str1 ->
                      fun pos1 ->
                        fun str2 ->
                          fun pos2 ->
                            fun lb ->
                              let _loc_lb = locate str1 pos1 str2 pos2 in
                              (lb, _loc_lb))))
             (fun x -> fun f -> fun l -> f (List.cons x l))))
       (Earley_core.Earley.fsequence_position
          (Earley_core.Earley.option None
             (Earley_core.Earley.apply (fun x -> Some x)
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ':' ':')
                   (Earley_core.Earley.fsequence typexpr
                      (Earley_core.Earley.empty (fun t -> t))))))
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '=' '=')
             (Earley_core.Earley.fsequence_position expression
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun e ->
                                      let _loc_e = locate str1 pos1 str2 pos2 in
                                      fun str1 ->
                                        fun pos1 ->
                                          fun str2 ->
                                            fun pos2 ->
                                              fun ty ->
                                                let _loc_ty =
                                                  locate str1 pos1 str2 pos2 in
                                                fun l ->
                                                  let e =
                                                    match ty with
                                                    | None -> e
                                                    | Some ty ->
                                                        Exp.constraint_
                                                          ~loc:(ghost
                                                                  (merge2
                                                                    _loc_ty
                                                                    _loc)) e
                                                          ty in
                                                  apply_params ~gh:true
                                                    _loc_e l e))))))
let eright_member = Earley_core.Earley.declare_grammar "eright_member"
let _ =
  Earley_core.Earley.set_grammar eright_member
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x)
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ':' ':')
                (Earley_core.Earley.fsequence typexpr
                   (Earley_core.Earley.empty (fun t -> t))))))
       (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '=' '=')
          (Earley_core.Earley.fsequence expression
             (Earley_core.Earley.empty (fun e -> fun ty -> (ty, e))))))
let _ =
  set_grammar let_binding
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_position value_name
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char ':' ':')
                (Earley_core.Earley.fsequence poly_syntax_typexpr
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '=' '=')
                      (Earley_core.Earley.fsequence_position expression
                         (Earley_core.Earley.fsequence post_item_attributes
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.option []
                                  (Earley_core.Earley.fsequence_ignore and_kw
                                     (Earley_core.Earley.fsequence
                                        let_binding
                                        (Earley_core.Earley.empty
                                           (fun _default_0 -> _default_0)))))
                               (Earley_core.Earley.empty
                                  (fun l ->
                                     fun a ->
                                       fun str1 ->
                                         fun pos1 ->
                                           fun str2 ->
                                             fun pos2 ->
                                               fun e ->
                                                 let _loc_e =
                                                   locate str1 pos1 str2 pos2 in
                                                 fun
                                                   ((ids, ty) as _default_0)
                                                   ->
                                                   fun str1 ->
                                                     fun pos1 ->
                                                       fun str2 ->
                                                         fun pos2 ->
                                                           fun vn ->
                                                             let _loc_vn =
                                                               locate str1
                                                                 pos1 str2
                                                                 pos2 in
                                                             let loc =
                                                               merge2 _loc_vn
                                                                 _loc_e in
                                                             let (e, ty) =
                                                               wrap_type_annotation
                                                                 loc ids ty e in
                                                             let pat =
                                                               Pat.constraint_
                                                                 ~loc:(
                                                                 ghost loc)
                                                                 (Pat.var
                                                                    ~loc:_loc_vn
                                                                    (
                                                                    id_loc vn
                                                                    _loc_vn))
                                                                 ty in
                                                             (Vb.mk ~loc
                                                                ~attrs:(
                                                                attach_attrib
                                                                  loc a) pat
                                                                e)
                                                               :: l)))))))))
          (List.cons
             (Earley_core.Earley.fsequence_position pattern
                (Earley_core.Earley.fsequence_position eright_member
                   (Earley_core.Earley.fsequence post_item_attributes
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.option []
                            (Earley_core.Earley.fsequence_ignore and_kw
                               (Earley_core.Earley.fsequence let_binding
                                  (Earley_core.Earley.empty
                                     (fun _default_0 -> _default_0)))))
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun l ->
                                       fun a ->
                                         fun str1 ->
                                           fun pos1 ->
                                             fun str2 ->
                                               fun pos2 ->
                                                 fun erm ->
                                                   let _loc_erm =
                                                     locate str1 pos1 str2
                                                       pos2 in
                                                   fun str1 ->
                                                     fun pos1 ->
                                                       fun str2 ->
                                                         fun pos2 ->
                                                           fun pat ->
                                                             let _loc_pat =
                                                               locate str1
                                                                 pos1 str2
                                                                 pos2 in
                                                             let (_ty, e) =
                                                               erm in
                                                             let loc =
                                                               merge2
                                                                 _loc_pat
                                                                 _loc_erm in
                                                             let (pat, e) =
                                                               match _ty with
                                                               | None ->
                                                                   (pat, e)
                                                               | Some ty ->
                                                                   let loc =
                                                                    ghost
                                                                    _loc in
                                                                   let poly_ty
                                                                    =
                                                                    Typ.poly
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc) []
                                                                    ty in
                                                                   ((Pat.constraint_
                                                                    ~loc pat
                                                                    poly_ty),
                                                                    (Exp.constraint_
                                                                    ~loc e ty)) in
                                                             (Vb.mk ~loc
                                                                ~attrs:(
                                                                attach_attrib
                                                                  loc a) pat
                                                                e)
                                                               :: l))))))
             (List.cons
                (Earley_core.Earley.fsequence_position value_name
                   (Earley_core.Earley.fsequence_position right_member
                      (Earley_core.Earley.fsequence post_item_attributes
                         (Earley_core.Earley.fsequence
                            (Earley_core.Earley.option []
                               (Earley_core.Earley.fsequence_ignore and_kw
                                  (Earley_core.Earley.fsequence let_binding
                                     (Earley_core.Earley.empty
                                        (fun _default_0 -> _default_0)))))
                            (Earley_core.Earley.empty
                               (fun l ->
                                  fun a ->
                                    fun str1 ->
                                      fun pos1 ->
                                        fun str2 ->
                                          fun pos2 ->
                                            fun e ->
                                              let _loc_e =
                                                locate str1 pos1 str2 pos2 in
                                              fun str1 ->
                                                fun pos1 ->
                                                  fun str2 ->
                                                    fun pos2 ->
                                                      fun vn ->
                                                        let _loc_vn =
                                                          locate str1 pos1
                                                            str2 pos2 in
                                                        let loc =
                                                          merge2 _loc_vn
                                                            _loc_e in
                                                        let pat =
                                                          Pat.var
                                                            ~loc:_loc_vn
                                                            (id_loc vn
                                                               _loc_vn) in
                                                        (Vb.mk ~loc
                                                           ~attrs:(attach_attrib
                                                                    loc a)
                                                           pat e)
                                                          :: l))))))
                (List.cons
                   (Earley_core.Earley.fsequence_position value_name
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char ':' ':')
                         (Earley_core.Earley.fsequence only_poly_typexpr
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '=' '=')
                               (Earley_core.Earley.fsequence_position
                                  expression
                                  (Earley_core.Earley.fsequence
                                     post_item_attributes
                                     (Earley_core.Earley.fsequence
                                        (Earley_core.Earley.option []
                                           (Earley_core.Earley.fsequence_ignore
                                              and_kw
                                              (Earley_core.Earley.fsequence
                                                 let_binding
                                                 (Earley_core.Earley.empty
                                                    (fun _default_0 ->
                                                       _default_0)))))
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun l ->
                                                      fun a ->
                                                        fun str1 ->
                                                          fun pos1 ->
                                                            fun str2 ->
                                                              fun pos2 ->
                                                                fun e ->
                                                                  let _loc_e
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                  fun ty ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun vn ->
                                                                    let _loc_vn
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    let pat =
                                                                    Pat.constraint_
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc)
                                                                    (Pat.var
                                                                    ~loc:_loc_vn
                                                                    (id_loc
                                                                    vn
                                                                    _loc_vn))
                                                                    (Typ.mk
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc)
                                                                    ty.ptyp_desc) in
                                                                    let loc =
                                                                    merge2
                                                                    _loc_vn
                                                                    _loc_e in
                                                                    (Vb.mk
                                                                    ~loc
                                                                    ~attrs:(
                                                                    attach_attrib
                                                                    loc a)
                                                                    pat e) ::
                                                                    l)))))))))
                   [])))))
let (match_case, match_case__set__grammar) =
  Earley_core.Earley.grammar_family "match_case"
let match_case __curry__varx0 __curry__varx1 =
  match_case (__curry__varx0, __curry__varx1)
let _ =
  match_case__set__grammar
    (fun (alm, lvl) ->
       Earley_core.Earley.fsequence pattern
         (Earley_core.Earley.fsequence
            (Earley_core.Earley.option None
               (Earley_core.Earley.apply (fun x -> Some x)
                  (Earley_core.Earley.fsequence_ignore when_kw
                     (Earley_core.Earley.fsequence expression
                        (Earley_core.Earley.empty
                           (fun _default_0 -> _default_0))))))
            (Earley_core.Earley.fsequence arrow_re
               (Earley_core.Earley.fsequence
                  (Earley_core.Earley.alternatives
                     (List.cons
                        (Earley_core.Earley.fsequence_ignore
                           (Earley_core.Earley.string "." ".")
                           (Earley_core.Earley.empty_pos
                              (fun __loc__start__buf ->
                                 fun __loc__start__pos ->
                                   fun __loc__end__buf ->
                                     fun __loc__end__pos ->
                                       let _loc =
                                         locate __loc__start__buf
                                           __loc__start__pos __loc__end__buf
                                           __loc__end__pos in
                                       Exp.unreachable ~loc:_loc ())))
                        (List.cons (expression_lvl (alm, lvl)) [])))
                  (Earley_core.Earley.empty
                     (fun e ->
                        fun _default_0 ->
                          fun guard -> fun pat -> Exp.case pat ?guard e))))))
let _ =
  set_grammar match_cases
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty []))
          (List.cons
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.option None
                   (Earley_core.Earley.apply (fun x -> Some x)
                      (Earley_core.Earley.char '|' '|')))
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.apply (fun f -> f [])
                      (Earley_core.Earley.fixpoint' (fun l -> l)
                         (Earley_core.Earley.fsequence (match_case Let Seq)
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '|' '|')
                               (Earley_core.Earley.empty
                                  (fun _default_0 -> _default_0))))
                         (fun x -> fun f -> fun l -> f (List.cons x l))))
                   (Earley_core.Earley.fsequence (match_case Match Seq)
                      (Earley_core.Earley.fsequence no_semi
                         (Earley_core.Earley.empty
                            (fun _default_0 ->
                               fun x -> fun l -> fun _default_1 -> l @ [x]))))))
             [])))
let type_coercion = Earley_core.Earley.declare_grammar "type_coercion"
let _ =
  Earley_core.Earley.set_grammar type_coercion
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.string ":>" ":>")
             (Earley_core.Earley.fsequence typexpr
                (Earley_core.Earley.empty (fun t' -> (None, (Some t'))))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string ":" ":")
                (Earley_core.Earley.fsequence typexpr
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x)
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.string ":>" ":>")
                               (Earley_core.Earley.fsequence typexpr
                                  (Earley_core.Earley.empty (fun t' -> t'))))))
                      (Earley_core.Earley.empty
                         (fun t' -> fun t -> ((Some t), t')))))) [])))
let expression_list = Earley_core.Earley.declare_grammar "expression_list"
let _ =
  Earley_core.Earley.set_grammar expression_list
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty []))
          (List.cons
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.apply (fun f -> f [])
                   (Earley_core.Earley.fixpoint' (fun l -> l)
                      (Earley_core.Earley.fsequence_position
                         (expression_lvl (NoMatch, (next_exp Seq)))
                         (Earley_core.Earley.fsequence_ignore semi_col
                            (Earley_core.Earley.empty
                               (fun str1 ->
                                  fun pos1 ->
                                    fun str2 ->
                                      fun pos2 ->
                                        fun e ->
                                          let _loc_e =
                                            locate str1 pos1 str2 pos2 in
                                          (e, _loc_e)))))
                      (fun x -> fun f -> fun l -> f (List.cons x l))))
                (Earley_core.Earley.fsequence_position
                   (expression_lvl (Match, (next_exp Seq)))
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x) semi_col))
                      (Earley_core.Earley.empty
                         (fun _default_0 ->
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun e ->
                                      let _loc_e = locate str1 pos1 str2 pos2 in
                                      fun l -> l @ [(e, _loc_e)]))))) [])))
let record_item = Earley_core.Earley.declare_grammar "record_item"
let _ =
  Earley_core.Earley.set_grammar record_item
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_position lident
             (Earley_core.Earley.empty
                (fun str1 ->
                   fun pos1 ->
                     fun str2 ->
                       fun pos2 ->
                         fun f ->
                           let _loc_f = locate str1 pos1 str2 pos2 in
                           let id = id_loc (Lident f) _loc_f in
                           (id, (Exp.ident ~loc:_loc_f id)))))
          (List.cons
             (Earley_core.Earley.fsequence_position field
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '=' '=')
                   (Earley_core.Earley.fsequence
                      (expression_lvl (NoMatch, (next_exp Seq)))
                      (Earley_core.Earley.empty
                         (fun e ->
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun f ->
                                      let _loc_f = locate str1 pos1 str2 pos2 in
                                      ((id_loc f _loc_f), e)))))) [])))
let last_record_item = Earley_core.Earley.declare_grammar "last_record_item"
let _ =
  Earley_core.Earley.set_grammar last_record_item
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_position lident
             (Earley_core.Earley.empty
                (fun str1 ->
                   fun pos1 ->
                     fun str2 ->
                       fun pos2 ->
                         fun f ->
                           let _loc_f = locate str1 pos1 str2 pos2 in
                           let id = id_loc (Lident f) _loc_f in
                           (id, (Exp.ident ~loc:_loc_f id)))))
          (List.cons
             (Earley_core.Earley.fsequence_position field
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '=' '=')
                   (Earley_core.Earley.fsequence
                      (expression_lvl (Match, (next_exp Seq)))
                      (Earley_core.Earley.empty
                         (fun e ->
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun f ->
                                      let _loc_f = locate str1 pos1 str2 pos2 in
                                      ((id_loc f _loc_f), e)))))) [])))
let _ =
  set_grammar record_list
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty []))
          (List.cons
             (Earley_core.Earley.fsequence
                (Earley_core.Earley.apply (fun f -> f [])
                   (Earley_core.Earley.fixpoint' (fun l -> l)
                      (Earley_core.Earley.fsequence record_item
                         (Earley_core.Earley.fsequence_ignore semi_col
                            (Earley_core.Earley.empty
                               (fun _default_0 -> _default_0))))
                      (fun x -> fun f -> fun l -> f (List.cons x l))))
                (Earley_core.Earley.fsequence last_record_item
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x) semi_col))
                      (Earley_core.Earley.empty
                         (fun _default_0 -> fun it -> fun l -> l @ [it])))))
             [])))
let obj_item = Earley_core.Earley.declare_grammar "obj_item"
let _ =
  Earley_core.Earley.set_grammar obj_item
    (Earley_core.Earley.fsequence_position inst_var_name
       (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '=' '=')
          (Earley_core.Earley.fsequence
             (expression_lvl (Match, (next_exp Seq)))
             (Earley_core.Earley.empty
                (fun e ->
                   fun str1 ->
                     fun pos1 ->
                       fun str2 ->
                         fun pos2 ->
                           fun v ->
                             let _loc_v = locate str1 pos1 str2 pos2 in
                             ((id_loc v _loc_v), e))))))
let class_expr_base = Earley_core.Earley.declare_grammar "class_expr_base"
let _ =
  Earley_core.Earley.set_grammar class_expr_base
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence object_kw
             (Earley_core.Earley.fsequence class_body
                (Earley_core.Earley.fsequence end_kw
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun _default_0 ->
                                 fun cb ->
                                   fun _default_1 ->
                                     Cl.structure ~loc:_loc cb)))))
          (List.cons
             (Earley_core.Earley.fsequence_position class_path
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun cp ->
                                      let _loc_cp =
                                        locate str1 pos1 str2 pos2 in
                                      Cl.constr ~loc:_loc (id_loc cp _loc_cp)
                                        [])))
             (List.cons
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char '[' '[')
                   (Earley_core.Earley.fsequence typexpr
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.apply (fun f -> f [])
                            (Earley_core.Earley.fixpoint' (fun l -> l)
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ',' ',')
                                  (Earley_core.Earley.fsequence typexpr
                                     (Earley_core.Earley.empty (fun te -> te))))
                               (fun x -> fun f -> fun l -> f (List.cons x l))))
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ']' ']')
                            (Earley_core.Earley.fsequence_position class_path
                               (Earley_core.Earley.empty_pos
                                  (fun __loc__start__buf ->
                                     fun __loc__start__pos ->
                                       fun __loc__end__buf ->
                                         fun __loc__end__pos ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           fun str1 ->
                                             fun pos1 ->
                                               fun str2 ->
                                                 fun pos2 ->
                                                   fun cp ->
                                                     let _loc_cp =
                                                       locate str1 pos1 str2
                                                         pos2 in
                                                     fun tes ->
                                                       fun te ->
                                                         Cl.constr ~loc:_loc
                                                           (id_loc cp _loc_cp)
                                                           (te :: tes))))))))
                (List.cons
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '(' '(')
                      (Earley_core.Earley.fsequence class_expr
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ')' ')')
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun ce -> Cl.mk ~loc:_loc ce.pcl_desc)))))
                   (List.cons
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '(' '(')
                         (Earley_core.Earley.fsequence class_expr
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.string ":" ":")
                               (Earley_core.Earley.fsequence class_type
                                  (Earley_core.Earley.fsequence_ignore
                                     (Earley_core.Earley.char ')' ')')
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun ct ->
                                                   fun ce ->
                                                     Cl.constraint_ ~loc:_loc
                                                       ce ct)))))))
                      (List.cons
                         (Earley_core.Earley.fsequence fun_kw
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.apply (fun f -> f [])
                                  (Earley_core.Earley.fixpoint1' (fun l -> l)
                                     (Earley_core.Earley.fsequence
                                        (parameter false)
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun p -> (p, _loc))))
                                     (fun x ->
                                        fun f -> fun l -> f (List.cons x l))))
                               (Earley_core.Earley.fsequence arrow_re
                                  (Earley_core.Earley.fsequence class_expr
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun ce ->
                                                   fun _default_0 ->
                                                     fun ps ->
                                                       fun _default_1 ->
                                                         apply_params_cls
                                                           _loc ps ce))))))
                         (List.cons
                            (Earley_core.Earley.fsequence let_kw
                               (Earley_core.Earley.fsequence rec_flag
                                  (Earley_core.Earley.fsequence let_binding
                                     (Earley_core.Earley.fsequence in_kw
                                        (Earley_core.Earley.fsequence
                                           class_expr
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun ce ->
                                                         fun _default_0 ->
                                                           fun lbs ->
                                                             fun r ->
                                                               fun _default_1
                                                                 ->
                                                                 Cl.let_
                                                                   ~loc:_loc
                                                                   r lbs ce)))))))
                            []))))))))
let _ =
  set_grammar class_expr
    (Earley_core.Earley.fsequence class_expr_base
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.option None
             (Earley_core.Earley.apply (fun x -> Some x)
                (Earley_core.Earley.apply (fun f -> f [])
                   (Earley_core.Earley.fixpoint1' (fun l -> l) argument
                      (fun x -> fun f -> fun l -> f (List.cons x l))))))
          (Earley_core.Earley.empty_pos
             (fun __loc__start__buf ->
                fun __loc__start__pos ->
                  fun __loc__end__buf ->
                    fun __loc__end__pos ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      fun args ->
                        fun ce ->
                          match args with
                          | None -> ce
                          | Some l -> Cl.apply ~loc:_loc ce l))))
let class_field = Earley_core.Earley.declare_grammar "class_field"
let _ =
  Earley_core.Earley.set_grammar class_field
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence floating_extension
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun ext -> Cf.extension ~loc:_loc ext)))
          (List.cons
             (Earley_core.Earley.fsequence inherit_kw
                (Earley_core.Earley.fsequence override_flag
                   (Earley_core.Earley.fsequence class_expr
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.option None
                            (Earley_core.Earley.apply (fun x -> Some x)
                               (Earley_core.Earley.fsequence_ignore as_kw
                                  (Earley_core.Earley.fsequence_position
                                     lident
                                     (Earley_core.Earley.empty
                                        (fun str1 ->
                                           fun pos1 ->
                                             fun str2 ->
                                               fun pos2 ->
                                                 fun id ->
                                                   let _loc_id =
                                                     locate str1 pos1 str2
                                                       pos2 in
                                                   id_loc id _loc_id))))))
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun id ->
                                       fun ce ->
                                         fun o ->
                                           fun _default_0 ->
                                             Cf.inherit_ ~loc:_loc o ce id))))))
             (List.cons
                (Earley_core.Earley.fsequence val_kw
                   (Earley_core.Earley.fsequence override_flag
                      (Earley_core.Earley.fsequence mutable_flag
                         (Earley_core.Earley.fsequence_position inst_var_name
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.option None
                                  (Earley_core.Earley.apply (fun x -> Some x)
                                     (Earley_core.Earley.fsequence_ignore
                                        (Earley_core.Earley.char ':' ':')
                                        (Earley_core.Earley.fsequence typexpr
                                           (Earley_core.Earley.empty
                                              (fun t -> t))))))
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char '=' '=')
                                  (Earley_core.Earley.fsequence expression
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun e ->
                                                   fun te ->
                                                     fun str1 ->
                                                       fun pos1 ->
                                                         fun str2 ->
                                                           fun pos2 ->
                                                             fun ivn ->
                                                               let _loc_ivn =
                                                                 locate str1
                                                                   pos1 str2
                                                                   pos2 in
                                                               fun m ->
                                                                 fun o ->
                                                                   fun
                                                                    _default_0
                                                                    ->
                                                                    let ivn =
                                                                    id_loc
                                                                    ivn
                                                                    _loc_ivn in
                                                                    let ex =
                                                                    match te
                                                                    with
                                                                    | 
                                                                    None -> e
                                                                    | 
                                                                    Some t ->
                                                                    Exp.constraint_
                                                                    ~loc:(
                                                                    ghost
                                                                    (merge2
                                                                    _loc_ivn
                                                                    _loc)) e
                                                                    t in
                                                                    Cf.val_
                                                                    ~loc:_loc
                                                                    ivn m
                                                                    (Cfk_concrete
                                                                    (o, ex)))))))))))
                (List.cons
                   (Earley_core.Earley.fsequence val_kw
                      (Earley_core.Earley.fsequence mutable_flag
                         (Earley_core.Earley.fsequence virtual_kw
                            (Earley_core.Earley.fsequence_position
                               inst_var_name
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ':' ':')
                                  (Earley_core.Earley.fsequence typexpr
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun te ->
                                                   fun str1 ->
                                                     fun pos1 ->
                                                       fun str2 ->
                                                         fun pos2 ->
                                                           fun ivn ->
                                                             let _loc_ivn =
                                                               locate str1
                                                                 pos1 str2
                                                                 pos2 in
                                                             fun _default_0
                                                               ->
                                                               fun m ->
                                                                 fun
                                                                   _default_1
                                                                   ->
                                                                   Cf.val_
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    ivn
                                                                    _loc_ivn)
                                                                    m
                                                                    (Cfk_virtual
                                                                    te)))))))))
                   (List.cons
                      (Earley_core.Earley.fsequence val_kw
                         (Earley_core.Earley.fsequence virtual_kw
                            (Earley_core.Earley.fsequence mutable_kw
                               (Earley_core.Earley.fsequence_position
                                  inst_var_name
                                  (Earley_core.Earley.fsequence_ignore
                                     (Earley_core.Earley.char ':' ':')
                                     (Earley_core.Earley.fsequence typexpr
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun te ->
                                                      fun str1 ->
                                                        fun pos1 ->
                                                          fun str2 ->
                                                            fun pos2 ->
                                                              fun ivn ->
                                                                let _loc_ivn
                                                                  =
                                                                  locate str1
                                                                    pos1 str2
                                                                    pos2 in
                                                                fun
                                                                  _default_0
                                                                  ->
                                                                  fun
                                                                    _default_1
                                                                    ->
                                                                    fun
                                                                    _default_2
                                                                    ->
                                                                    Cf.val_
                                                                    ~loc:_loc
                                                                    (id_loc
                                                                    ivn
                                                                    _loc_ivn)
                                                                    Mutable
                                                                    (Cfk_virtual
                                                                    te)))))))))
                      (List.cons
                         (Earley_core.Earley.fsequence method_kw
                            (Earley_core.Earley.fsequence_position
                               (Earley_core.Earley.fsequence override_flag
                                  (Earley_core.Earley.fsequence private_flag
                                     (Earley_core.Earley.fsequence
                                        method_name
                                        (Earley_core.Earley.empty
                                           (fun _default_0 ->
                                              fun _default_1 ->
                                                fun _default_2 ->
                                                  (_default_2, _default_1,
                                                    _default_0))))))
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ':' ':')
                                  (Earley_core.Earley.fsequence poly_typexpr
                                     (Earley_core.Earley.fsequence_ignore
                                        (Earley_core.Earley.char '=' '=')
                                        (Earley_core.Earley.fsequence
                                           expression
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun e ->
                                                         fun te ->
                                                           fun str1 ->
                                                             fun pos1 ->
                                                               fun str2 ->
                                                                 fun pos2 ->
                                                                   fun t ->
                                                                    let _loc_t
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let 
                                                                    (o, p,
                                                                    mn) = t in
                                                                    let e =
                                                                    Exp.poly
                                                                    ~loc:(
                                                                    ghost
                                                                    (merge2
                                                                    _loc_t
                                                                    _loc)) e
                                                                    (Some te) in
                                                                    Cf.method_
                                                                    ~loc:_loc
                                                                    mn p
                                                                    (Cfk_concrete
                                                                    (o, e))))))))))
                         (List.cons
                            (Earley_core.Earley.fsequence method_kw
                               (Earley_core.Earley.fsequence_position
                                  (Earley_core.Earley.fsequence override_flag
                                     (Earley_core.Earley.fsequence
                                        private_flag
                                        (Earley_core.Earley.fsequence
                                           method_name
                                           (Earley_core.Earley.empty
                                              (fun _default_0 ->
                                                 fun _default_1 ->
                                                   fun _default_2 ->
                                                     (_default_2, _default_1,
                                                       _default_0))))))
                                  (Earley_core.Earley.fsequence_ignore
                                     (Earley_core.Earley.string ":" ":")
                                     (Earley_core.Earley.fsequence
                                        poly_syntax_typexpr
                                        (Earley_core.Earley.fsequence_ignore
                                           (Earley_core.Earley.char '=' '=')
                                           (Earley_core.Earley.fsequence_position
                                              expression
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun str1 ->
                                                            fun pos1 ->
                                                              fun str2 ->
                                                                fun pos2 ->
                                                                  fun e ->
                                                                    let _loc_e
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    ((ids,
                                                                    te) as
                                                                    _default_0)
                                                                    ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun t ->
                                                                    let _loc_t
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    let 
                                                                    (o, p,
                                                                    mn) = t in
                                                                    let _loc_e
                                                                    =
                                                                    merge2
                                                                    _loc_t
                                                                    _loc in
                                                                    let 
                                                                    (e, poly)
                                                                    =
                                                                    wrap_type_annotation
                                                                    _loc_e
                                                                    ids te e in
                                                                    let e =
                                                                    Exp.poly
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc_e) e
                                                                    (Some
                                                                    poly) in
                                                                    Cf.method_
                                                                    ~loc:_loc
                                                                    mn p
                                                                    (Cfk_concrete
                                                                    (o, e))))))))))
                            (List.cons
                               (Earley_core.Earley.fsequence method_kw
                                  (Earley_core.Earley.fsequence_position
                                     (Earley_core.Earley.fsequence
                                        override_flag
                                        (Earley_core.Earley.fsequence
                                           private_flag
                                           (Earley_core.Earley.fsequence
                                              method_name
                                              (Earley_core.Earley.empty
                                                 (fun _default_0 ->
                                                    fun _default_1 ->
                                                      fun _default_2 ->
                                                        (_default_2,
                                                          _default_1,
                                                          _default_0))))))
                                     (Earley_core.Earley.fsequence
                                        (Earley_core.Earley.apply
                                           (fun f -> f [])
                                           (Earley_core.Earley.fixpoint'
                                              (fun l -> l)
                                              (Earley_core.Earley.fsequence_position
                                                 (parameter true)
                                                 (Earley_core.Earley.empty
                                                    (fun str1 ->
                                                       fun pos1 ->
                                                         fun str2 ->
                                                           fun pos2 ->
                                                             fun p ->
                                                               let _loc_p =
                                                                 locate str1
                                                                   pos1 str2
                                                                   pos2 in
                                                               (p, _loc_p))))
                                              (fun x ->
                                                 fun f ->
                                                   fun l -> f (List.cons x l))))
                                        (Earley_core.Earley.fsequence_position
                                           (Earley_core.Earley.option None
                                              (Earley_core.Earley.apply
                                                 (fun x -> Some x)
                                                 (Earley_core.Earley.fsequence_ignore
                                                    (Earley_core.Earley.char
                                                       ':' ':')
                                                    (Earley_core.Earley.fsequence
                                                       typexpr
                                                       (Earley_core.Earley.empty
                                                          (fun te -> te))))))
                                           (Earley_core.Earley.fsequence_ignore
                                              (Earley_core.Earley.char '='
                                                 '=')
                                              (Earley_core.Earley.fsequence_position
                                                 expression
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
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
                                                             fun str1 ->
                                                               fun pos1 ->
                                                                 fun str2 ->
                                                                   fun pos2
                                                                    ->
                                                                    fun e ->
                                                                    let _loc_e
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun te ->
                                                                    let _loc_te
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun ps ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun t ->
                                                                    let _loc_t
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let 
                                                                    (o, p,
                                                                    mn) = t in
                                                                    if
                                                                    (ps = [])
                                                                    &&
                                                                    (te <>
                                                                    None)
                                                                    then
                                                                    give_up
                                                                    ();
                                                                    (
                                                                    let e =
                                                                    match te
                                                                    with
                                                                    | 
                                                                    None -> e
                                                                    | 
                                                                    Some te
                                                                    ->
                                                                    Exp.constraint_
                                                                    ~loc:(
                                                                    ghost
                                                                    (merge2
                                                                    _loc_te
                                                                    _loc_e))
                                                                    e te in
                                                                    let e
                                                                    : expression
                                                                    =
                                                                    apply_params
                                                                    ~gh:true
                                                                    _loc_e ps
                                                                    e in
                                                                    let e =
                                                                    Exp.poly
                                                                    ~loc:(
                                                                    ghost
                                                                    (merge2
                                                                    _loc_t
                                                                    _loc_e))
                                                                    e None in
                                                                    Cf.method_
                                                                    ~loc:_loc
                                                                    mn p
                                                                    (Cfk_concrete
                                                                    (o, e)))))))))))
                               (List.cons
                                  (Earley_core.Earley.fsequence method_kw
                                     (Earley_core.Earley.fsequence
                                        private_flag
                                        (Earley_core.Earley.fsequence
                                           virtual_kw
                                           (Earley_core.Earley.fsequence
                                              method_name
                                              (Earley_core.Earley.fsequence_ignore
                                                 (Earley_core.Earley.char ':'
                                                    ':')
                                                 (Earley_core.Earley.fsequence
                                                    poly_typexpr
                                                    (Earley_core.Earley.empty_pos
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
                                                                    __loc__end__pos in
                                                                fun pte ->
                                                                  fun mn ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun p ->
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    Cf.method_
                                                                    ~loc:_loc
                                                                    mn p
                                                                    (Cfk_virtual
                                                                    pte)))))))))
                                  (List.cons
                                     (Earley_core.Earley.fsequence method_kw
                                        (Earley_core.Earley.fsequence
                                           virtual_kw
                                           (Earley_core.Earley.fsequence
                                              private_kw
                                              (Earley_core.Earley.fsequence
                                                 method_name
                                                 (Earley_core.Earley.fsequence_ignore
                                                    (Earley_core.Earley.char
                                                       ':' ':')
                                                    (Earley_core.Earley.fsequence
                                                       poly_typexpr
                                                       (Earley_core.Earley.empty_pos
                                                          (fun
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
                                                                   fun pte ->
                                                                    fun mn ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    fun
                                                                    _default_2
                                                                    ->
                                                                    Cf.method_
                                                                    ~loc:_loc
                                                                    mn
                                                                    Private
                                                                    (Cfk_virtual
                                                                    pte)))))))))
                                     (List.cons
                                        (Earley_core.Earley.fsequence
                                           constraint_kw
                                           (Earley_core.Earley.fsequence
                                              typexpr
                                              (Earley_core.Earley.fsequence_ignore
                                                 (Earley_core.Earley.char '='
                                                    '=')
                                                 (Earley_core.Earley.fsequence
                                                    typexpr
                                                    (Earley_core.Earley.empty_pos
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
                                                                    __loc__end__pos in
                                                                fun te' ->
                                                                  fun te ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    Cf.constraint_
                                                                    ~loc:_loc
                                                                    te te'))))))
                                        (List.cons
                                           (Earley_core.Earley.fsequence
                                              initializer_kw
                                              (Earley_core.Earley.fsequence
                                                 expression
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
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
                                                             fun e ->
                                                               fun _default_0
                                                                 ->
                                                                 Cf.initializer_
                                                                   ~loc:_loc
                                                                   e))))
                                           (List.cons
                                              (Earley_core.Earley.fsequence
                                                 floating_attribute
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
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
                                                             fun attr ->
                                                               Cf.attribute
                                                                 ~loc:_loc
                                                                 attr))) []))))))))))))))
let _ =
  set_grammar class_body
    (Earley_core.Earley.fsequence_position
       (Earley_core.Earley.option None
          (Earley_core.Earley.apply (fun x -> Some x) pattern))
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l) class_field
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.empty
             (fun fs ->
                fun str1 ->
                  fun pos1 ->
                    fun str2 ->
                      fun pos2 ->
                        fun p ->
                          let _loc_p = locate str1 pos1 str2 pos2 in
                          let p =
                            match p with
                            | None -> Pat.any ~loc:(ghost _loc_p) ()
                            | Some p -> p in
                          Cstr.mk p fs))))
let class_binding = Earley_core.Earley.declare_grammar "class_binding"
let _ =
  Earley_core.Earley.set_grammar class_binding
    (Earley_core.Earley.fsequence virtual_flag
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.option []
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '[' '[')
                (Earley_core.Earley.fsequence type_parameters
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char ']' ']')
                      (Earley_core.Earley.empty (fun params -> params))))))
          (Earley_core.Earley.fsequence_position class_name
             (Earley_core.Earley.fsequence_position
                (Earley_core.Earley.apply (fun f -> f [])
                   (Earley_core.Earley.fixpoint' (fun l -> l)
                      (Earley_core.Earley.fsequence (parameter false)
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun p -> (p, _loc))))
                      (fun x -> fun f -> fun l -> f (List.cons x l))))
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.option None
                      (Earley_core.Earley.apply (fun x -> Some x)
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char ':' ':')
                            (Earley_core.Earley.fsequence class_type
                               (Earley_core.Earley.empty (fun ct -> ct))))))
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char '=' '=')
                      (Earley_core.Earley.fsequence class_expr
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun ce ->
                                       fun ct ->
                                         fun str1 ->
                                           fun pos1 ->
                                             fun str2 ->
                                               fun pos2 ->
                                                 fun ps ->
                                                   let _loc_ps =
                                                     locate str1 pos1 str2
                                                       pos2 in
                                                   fun str1 ->
                                                     fun pos1 ->
                                                       fun str2 ->
                                                         fun pos2 ->
                                                           fun cn ->
                                                             let _loc_cn =
                                                               locate str1
                                                                 pos1 str2
                                                                 pos2 in
                                                             fun params ->
                                                               fun virt ->
                                                                 let ce =
                                                                   apply_params_cls
                                                                    ~gh:true
                                                                    (merge2
                                                                    _loc_ps
                                                                    _loc) ps
                                                                    ce in
                                                                 let ce =
                                                                   match ct
                                                                   with
                                                                   | 
                                                                   None -> ce
                                                                   | 
                                                                   Some ct ->
                                                                    Cl.constraint_
                                                                    ~loc:_loc
                                                                    ce ct in
                                                                 fun _loc ->
                                                                   Ci.mk
                                                                    ~loc:_loc
                                                                    ~attrs:(
                                                                    attach_attrib
                                                                    _loc [])
                                                                    ~virt
                                                                    ~params
                                                                    (id_loc
                                                                    cn
                                                                    _loc_cn)
                                                                    ce)))))))))
let class_definition = Earley_core.Earley.declare_grammar "class_definition"
let _ =
  Earley_core.Earley.set_grammar class_definition
    (Earley_core.Earley.fsequence_position class_kw
       (Earley_core.Earley.fsequence_position class_binding
          (Earley_core.Earley.fsequence
             (Earley_core.Earley.apply (fun f -> f [])
                (Earley_core.Earley.fixpoint' (fun l -> l)
                   (Earley_core.Earley.fsequence_ignore and_kw
                      (Earley_core.Earley.fsequence class_binding
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun cb -> cb _loc))))
                   (fun x -> fun f -> fun l -> f (List.cons x l))))
             (Earley_core.Earley.empty
                (fun cbs ->
                   fun str1 ->
                     fun pos1 ->
                       fun str2 ->
                         fun pos2 ->
                           fun cb ->
                             let _loc_cb = locate str1 pos1 str2 pos2 in
                             fun str1 ->
                               fun pos1 ->
                                 fun str2 ->
                                   fun pos2 ->
                                     fun k ->
                                       let _loc_k =
                                         locate str1 pos1 str2 pos2 in
                                       (cb (merge2 _loc_k _loc_cb)) :: cbs)))))
let pexp_list _loc ?loc_cl  l =
  if l = []
  then Exp.construct ~loc:_loc (id_loc (Lident "[]") _loc) None
  else
    (let loc_cl = ghost (match loc_cl with | None -> _loc | Some pos -> pos) in
     List.fold_right
       (fun (x, pos) ->
          fun acc ->
            let _loc = ghost (merge2 pos loc_cl) in
            Exp.construct ~loc:_loc (id_loc (Lident "::") (ghost _loc))
              (Some (Exp.tuple ~loc:_loc [x; acc]))) l
       (Exp.construct ~loc:loc_cl (id_loc (Lident "[]") loc_cl) None))
let apply_lbl loc (lbl, e) =
  match e with
  | None -> (lbl, (Exp.ident ~loc (id_loc (Lident lbl) loc)))
  | Some e -> (lbl, e)
let rec mk_seq loc_c final l =
  match l with
  | [] -> final
  | x::l ->
      Exp.sequence ~loc:(merge2 x.pexp_loc loc_c) x (mk_seq loc_c final l)
let structure_item_simple = declare_grammar "structure_item_simple"
let functor_parameter =
  Earley_core.Earley.declare_grammar "functor_parameter"
let _ =
  Earley_core.Earley.set_grammar functor_parameter
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '(' '(')
             (Earley_core.Earley.fsequence module_name
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ':' ':')
                   (Earley_core.Earley.fsequence module_type
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char ')' ')')
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun mt ->
                                       fun mn -> (_loc, (Named (mn, mt))))))))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '(' '(')
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.char ')' ')')
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               (_loc, Unit))))) [])))
let (left_expr, left_expr__set__grammar) =
  Earley_core.Earley.grammar_prio "left_expr"
let (prefix_expr, prefix_expr__set__grammar) =
  Earley_core.Earley.grammar_family "prefix_expr"
let rec infix_expr lvl =
  if (assoc lvl) = Left
  then
    Earley_core.Earley.fsequence (expression_lvl (NoMatch, lvl))
      (Earley_core.Earley.fsequence_position (infix_symbol lvl)
         (Earley_core.Earley.empty
            (fun str1 ->
               fun pos1 ->
                 fun str2 ->
                   fun pos2 ->
                     fun op ->
                       let _loc_op = locate str1 pos1 str2 pos2 in
                       fun e' ->
                         ((next_exp lvl), false,
                           (fun e ->
                              fun (_l, _) -> mk_binary_op _l e' op _loc_op e)))))
  else
    if (assoc lvl) = NoAssoc
    then
      Earley_core.Earley.fsequence (expression_lvl (NoMatch, (next_exp lvl)))
        (Earley_core.Earley.fsequence_position (infix_symbol lvl)
           (Earley_core.Earley.empty
              (fun str1 ->
                 fun pos1 ->
                   fun str2 ->
                     fun pos2 ->
                       fun op ->
                         let _loc_op = locate str1 pos1 str2 pos2 in
                         fun e' ->
                           ((next_exp lvl), false,
                             (fun e ->
                                fun (_l, _) ->
                                  mk_binary_op _l e' op _loc_op e)))))
    else
      Earley_core.Earley.fsequence
        (Earley_core.Earley.apply (fun f -> f [])
           (Earley_core.Earley.fixpoint1' (fun l -> l)
              (Earley_core.Earley.fsequence
                 (expression_lvl (NoMatch, (next_exp lvl)))
                 (Earley_core.Earley.fsequence_position (infix_symbol lvl)
                    (Earley_core.Earley.empty_pos
                       (fun __loc__start__buf ->
                          fun __loc__start__pos ->
                            fun __loc__end__buf ->
                              fun __loc__end__pos ->
                                let _loc =
                                  locate __loc__start__buf __loc__start__pos
                                    __loc__end__buf __loc__end__pos in
                                fun str1 ->
                                  fun pos1 ->
                                    fun str2 ->
                                      fun pos2 ->
                                        fun op ->
                                          let _loc_op =
                                            locate str1 pos1 str2 pos2 in
                                          fun e' -> (_loc, e', op, _loc_op)))))
              (fun x -> fun f -> fun l -> f (List.cons x l))))
        (Earley_core.Earley.empty
           (fun ls ->
              ((next_exp lvl), false,
                (fun e ->
                   fun (_l, _) ->
                     List.fold_right
                       (fun (_loc_e, e', op, _loc_op) ->
                          fun acc ->
                            mk_binary_op (merge2 _loc_e _l) e' op _loc_op acc)
                       ls e))))
let _ =
  left_expr__set__grammar
    ((List.cons ((fun (alm, lvl) -> lvl <= Pow), (infix_expr Pow))
        (List.cons
           ((fun (alm, lvl) -> (allow_let alm) && (lvl < App)),
             (Earley_core.Earley.fsequence fun_kw
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.apply (fun f -> f [])
                      (Earley_core.Earley.fixpoint' (fun l -> l)
                         (Earley_core.Earley.fsequence_position
                            (parameter true)
                            (Earley_core.Earley.empty
                               (fun str1 ->
                                  fun pos1 ->
                                    fun str2 ->
                                      fun pos2 ->
                                        fun lbl ->
                                          let _loc_lbl =
                                            locate str1 pos1 str2 pos2 in
                                          (lbl, _loc_lbl))))
                         (fun x -> fun f -> fun l -> f (List.cons x l))))
                   (Earley_core.Earley.fsequence arrow_re
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun _default_0 ->
                                    fun l ->
                                      fun _default_1 ->
                                        (Seq, false,
                                          (fun e ->
                                             fun (_loc, _) ->
                                               Exp.mk ~loc:_loc
                                                 (apply_params _loc l e).pexp_desc))))))))
           (List.cons
              ((fun (alm, lvl) -> (allow_let alm) && (lvl < App)),
                (Earley_core.Earley.fsequence_ignore let_kw
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.alternatives
                         (List.cons
                            (Earley_core.Earley.fsequence open_kw
                               (Earley_core.Earley.fsequence override_flag
                                  (Earley_core.Earley.fsequence_position
                                     module_path
                                     (Earley_core.Earley.empty
                                        (fun str1 ->
                                           fun pos1 ->
                                             fun str2 ->
                                               fun pos2 ->
                                                 fun mp ->
                                                   let _loc_mp =
                                                     locate str1 pos1 str2
                                                       pos2 in
                                                   fun o ->
                                                     fun _default_0 ->
                                                       fun e ->
                                                         fun (_l, _) ->
                                                           let mp =
                                                             id_loc mp
                                                               _loc_mp in
                                                           Exp.open_ ~loc:_l
                                                             (Opn.mk
                                                                ~override:o
                                                                (Mod.ident mp))
                                                             e)))))
                            (List.cons
                               (Earley_core.Earley.fsequence rec_flag
                                  (Earley_core.Earley.fsequence let_binding
                                     (Earley_core.Earley.empty
                                        (fun l ->
                                           fun r ->
                                             fun e ->
                                               fun (loc, _) ->
                                                 Exp.let_ ~loc r l e))))
                               (List.cons
                                  (Earley_core.Earley.fsequence module_kw
                                     (Earley_core.Earley.fsequence
                                        module_name
                                        (Earley_core.Earley.fsequence
                                           (Earley_core.Earley.apply
                                              (fun f -> f [])
                                              (Earley_core.Earley.fixpoint'
                                                 (fun l -> l)
                                                 functor_parameter
                                                 (fun x ->
                                                    fun f ->
                                                      fun l ->
                                                        f (List.cons x l))))
                                           (Earley_core.Earley.fsequence_position
                                              (Earley_core.Earley.option None
                                                 (Earley_core.Earley.apply
                                                    (fun x -> Some x)
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.char
                                                          ':' ':')
                                                       (Earley_core.Earley.fsequence
                                                          module_type
                                                          (Earley_core.Earley.empty
                                                             (fun mt -> mt))))))
                                              (Earley_core.Earley.fsequence_ignore
                                                 (Earley_core.Earley.char '='
                                                    '=')
                                                 (Earley_core.Earley.fsequence_position
                                                    module_expr
                                                    (Earley_core.Earley.empty
                                                       (fun str1 ->
                                                          fun pos1 ->
                                                            fun str2 ->
                                                              fun pos2 ->
                                                                fun me ->
                                                                  let _loc_me
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                  fun str1 ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mt ->
                                                                    let _loc_mt
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun l ->
                                                                    fun mn ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun e ->
                                                                    fun
                                                                    (loc, _)
                                                                    ->
                                                                    let me =
                                                                    match mt
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    me
                                                                    | 
                                                                    Some mt
                                                                    ->
                                                                    let loc =
                                                                    merge2
                                                                    _loc_mt
                                                                    _loc_me in
                                                                    Mod.constraint_
                                                                    ~loc me
                                                                    mt in
                                                                    let me =
                                                                    List.fold_left
                                                                    (fun acc
                                                                    ->
                                                                    fun
                                                                    (loc, p)
                                                                    ->
                                                                    let loc =
                                                                    merge2
                                                                    loc
                                                                    _loc_me in
                                                                    Mod.functor_
                                                                    ~loc p
                                                                    acc) me
                                                                    (List.rev
                                                                    l) in
                                                                    Exp.letmodule
                                                                    ~loc mn
                                                                    me e))))))))
                                  []))))
                      (Earley_core.Earley.fsequence_ignore in_kw
                         (Earley_core.Earley.empty (fun f -> (Seq, false, f)))))))
              (List.cons
                 ((fun (alm, lvl) ->
                     ((allow_let alm) || (lvl = If)) && (lvl < App)),
                   (Earley_core.Earley.fsequence if_kw
                      (Earley_core.Earley.fsequence expression
                         (Earley_core.Earley.fsequence then_kw
                            (Earley_core.Earley.fsequence
                               (expression_lvl (Match, (next_exp Seq)))
                               (Earley_core.Earley.fsequence else_kw
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun _default_0 ->
                                                fun e ->
                                                  fun _default_1 ->
                                                    fun c ->
                                                      fun _default_2 ->
                                                        ((next_exp Seq),
                                                          false,
                                                          (fun e' ->
                                                             fun (_loc, _) ->
                                                               Exp.ifthenelse
                                                                 ~loc:_loc c
                                                                 e (Some e')))))))))))
                 (List.cons
                    ((fun (alm, lvl) ->
                        ((allow_let alm) || (lvl = If)) && (lvl < App)),
                      (Earley_core.Earley.fsequence if_kw
                         (Earley_core.Earley.fsequence expression
                            (Earley_core.Earley.fsequence then_kw
                               (Earley_core.Earley.empty_pos
                                  (fun __loc__start__buf ->
                                     fun __loc__start__pos ->
                                       fun __loc__end__buf ->
                                         fun __loc__end__pos ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           fun _default_0 ->
                                             fun c ->
                                               fun _default_1 ->
                                                 ((next_exp Seq), true,
                                                   (fun e ->
                                                      fun (_loc, _) ->
                                                        Exp.ifthenelse
                                                          ~loc:_loc c e None))))))))
                    (List.cons
                       ((fun (alm, lvl) -> lvl <= Seq),
                         (Earley_core.Earley.fsequence
                            (Earley_core.Earley.apply (fun f -> f [])
                               (Earley_core.Earley.fixpoint1' (fun l -> l)
                                  (Earley_core.Earley.fsequence
                                     (expression_lvl
                                        (NoMatch, (next_exp Seq)))
                                     (Earley_core.Earley.fsequence_ignore
                                        semi_col
                                        (Earley_core.Earley.empty
                                           (fun _default_0 -> _default_0))))
                                  (fun x ->
                                     fun f -> fun l -> f (List.cons x l))))
                            (Earley_core.Earley.empty
                               (fun ls ->
                                  ((next_exp Seq), false,
                                    (fun e' -> fun (_, _l) -> mk_seq _l e' ls))))))
                       (List.cons
                          ((fun (alm, lvl) -> lvl <= Aff),
                            (Earley_core.Earley.fsequence_position
                               inst_var_name
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.string "<-" "<-")
                                  (Earley_core.Earley.empty
                                     (fun str1 ->
                                        fun pos1 ->
                                          fun str2 ->
                                            fun pos2 ->
                                              fun v ->
                                                let _loc_v =
                                                  locate str1 pos1 str2 pos2 in
                                                ((next_exp Aff), false,
                                                  (fun e ->
                                                     fun (loc, _) ->
                                                       Exp.setinstvar ~loc
                                                         (id_loc v _loc_v) e)))))))
                          (List.cons
                             ((fun (alm, lvl) -> lvl <= Aff),
                               (Earley_core.Earley.fsequence
                                  (expression_lvl (NoMatch, Dot))
                                  (Earley_core.Earley.fsequence_ignore
                                     (Earley_core.Earley.char '.' '.')
                                     (Earley_core.Earley.fsequence
                                        (Earley_core.Earley.alternatives
                                           (List.cons
                                              (Earley_core.Earley.fsequence_position
                                                 field
                                                 (Earley_core.Earley.empty
                                                    (fun str1 ->
                                                       fun pos1 ->
                                                         fun str2 ->
                                                           fun pos2 ->
                                                             fun f ->
                                                               let _loc_f =
                                                                 locate str1
                                                                   pos1 str2
                                                                   pos2 in
                                                               fun e' ->
                                                                 fun e ->
                                                                   fun
                                                                    (loc, _)
                                                                    ->
                                                                    let f =
                                                                    id_loc f
                                                                    _loc_f in
                                                                    Exp.setfield
                                                                    ~loc e' f
                                                                    e)))
                                              (List.cons
                                                 (Earley_core.Earley.fsequence_ignore
                                                    (Earley_core.Earley.string
                                                       "(" "(")
                                                    (Earley_core.Earley.fsequence
                                                       expression
                                                       (Earley_core.Earley.fsequence_ignore
                                                          (Earley_core.Earley.string
                                                             ")" ")")
                                                          (Earley_core.Earley.empty
                                                             (fun f ->
                                                                fun e' ->
                                                                  fun e ->
                                                                    fun
                                                                    (_l, _)
                                                                    ->
                                                                    exp_apply
                                                                    _l
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _l))
                                                                    "Array"
                                                                    "set")
                                                                    [e';
                                                                    f;
                                                                    e])))))
                                                 (List.cons
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.string
                                                          "[" "[")
                                                       (Earley_core.Earley.fsequence
                                                          expression
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.string
                                                                "]" "]")
                                                             (Earley_core.Earley.empty
                                                                (fun f ->
                                                                   fun e' ->
                                                                    fun e ->
                                                                    fun
                                                                    (_l, _)
                                                                    ->
                                                                    exp_apply
                                                                    _l
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _l))
                                                                    "String"
                                                                    "set")
                                                                    [e';
                                                                    f;
                                                                    e])))))
                                                    (List.cons
                                                       (Earley_core.Earley.fsequence_ignore
                                                          (Earley_core.Earley.string
                                                             "{" "{")
                                                          (Earley_core.Earley.fsequence
                                                             expression
                                                             (Earley_core.Earley.fsequence_ignore
                                                                (Earley_core.Earley.string
                                                                   "}" "}")
                                                                (Earley_core.Earley.empty
                                                                   (fun f ->
                                                                    fun e' ->
                                                                    fun e ->
                                                                    fun
                                                                    (_l, _)
                                                                    ->
                                                                    de_ghost
                                                                    (bigarray_set
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _l)) e' f
                                                                    e))))))
                                                       [])))))
                                        (Earley_core.Earley.fsequence_ignore
                                           (Earley_core.Earley.string "<-"
                                              "<-")
                                           (Earley_core.Earley.empty
                                              (fun f ->
                                                 fun e' ->
                                                   ((next_exp Aff), false,
                                                     (f e')))))))))
                             (List.cons
                                ((fun (alm, lvl) -> lvl <= Tupl),
                                  (Earley_core.Earley.fsequence
                                     (Earley_core.Earley.apply
                                        (fun f -> f [])
                                        (Earley_core.Earley.fixpoint1'
                                           (fun l -> l)
                                           (Earley_core.Earley.fsequence
                                              (expression_lvl
                                                 (NoMatch, (next_exp Tupl)))
                                              (Earley_core.Earley.fsequence_ignore
                                                 (Earley_core.Earley.char ','
                                                    ',')
                                                 (Earley_core.Earley.empty
                                                    (fun _default_0 ->
                                                       _default_0))))
                                           (fun x ->
                                              fun f ->
                                                fun l -> f (List.cons x l))))
                                     (Earley_core.Earley.empty
                                        (fun l ->
                                           ((next_exp Tupl), false,
                                             (fun e' ->
                                                fun (_l, _) ->
                                                  Exp.tuple ~loc:_l
                                                    (l @ [e'])))))))
                                (List.cons
                                   ((fun (alm, lvl) -> lvl <= App),
                                     (Earley_core.Earley.fsequence assert_kw
                                        (Earley_core.Earley.empty
                                           (fun _default_0 ->
                                              ((next_exp App), false,
                                                (fun e ->
                                                   fun (loc, _) ->
                                                     Exp.assert_ ~loc e))))))
                                   (List.cons
                                      ((fun (alm, lvl) -> lvl <= App),
                                        (Earley_core.Earley.fsequence lazy_kw
                                           (Earley_core.Earley.empty
                                              (fun _default_0 ->
                                                 ((next_exp App), false,
                                                   (fun e ->
                                                      fun (loc, _) ->
                                                        Exp.lazy_ ~loc e))))))
                                      (List.cons
                                         ((fun (alm, lvl) -> lvl <= Opp),
                                           (prefix_expr Opp))
                                         (List.cons
                                            ((fun (alm, lvl) -> lvl <= Prefix),
                                              (prefix_expr Prefix))
                                            (List.cons
                                               ((fun (alm, lvl) ->
                                                   lvl <= Prod),
                                                 (infix_expr Prod))
                                               (List.cons
                                                  ((fun (alm, lvl) ->
                                                      lvl <= Sum),
                                                    (infix_expr Sum))
                                                  (List.cons
                                                     ((fun (alm, lvl) ->
                                                         lvl <= Append),
                                                       (infix_expr Append))
                                                     (List.cons
                                                        ((fun (alm, lvl) ->
                                                            lvl <= Cons),
                                                          (infix_expr Cons))
                                                        (List.cons
                                                           ((fun (alm, lvl)
                                                               -> lvl <= Aff),
                                                             (infix_expr Aff))
                                                           (List.cons
                                                              ((fun
                                                                  (alm, lvl)
                                                                  ->
                                                                  lvl <= Eq),
                                                                (infix_expr
                                                                   Eq))
                                                              (List.cons
                                                                 ((fun
                                                                    (alm,
                                                                    lvl) ->
                                                                    lvl <=
                                                                    Conj),
                                                                   (infix_expr
                                                                    Conj))
                                                                 (List.cons
                                                                    ((fun
                                                                    (alm,
                                                                    lvl) ->
                                                                    lvl <=
                                                                    Disj),
                                                                    (infix_expr
                                                                    Disj)) []))))))))))))))))))))),
      (fun (alm, lvl) -> []))
let _ =
  prefix_expr__set__grammar
    (fun lvl ->
       Earley_core.Earley.fsequence_position (prefix_symbol lvl)
         (Earley_core.Earley.empty
            (fun str1 ->
               fun pos1 ->
                 fun str2 ->
                   fun pos2 ->
                     fun p ->
                       let _loc_p = locate str1 pos1 str2 pos2 in
                       (lvl, false,
                         (fun e -> fun (_l, _) -> mk_unary_op _l p _loc_p e)))))
let prefix_expression =
  Earley_core.Earley.declare_grammar "prefix_expression"
let _ =
  Earley_core.Earley.set_grammar prefix_expression
    (Earley_core.Earley.alternatives
       (List.cons Pa_parser.extra_prefix_expressions
          (List.cons
             (Earley_core.Earley.fsequence function_kw
                (Earley_core.Earley.fsequence match_cases
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun l ->
                                 fun _default_0 -> Exp.function_ ~loc:_loc l))))
             (List.cons
                (Earley_core.Earley.fsequence match_kw
                   (Earley_core.Earley.fsequence expression
                      (Earley_core.Earley.fsequence with_kw
                         (Earley_core.Earley.fsequence match_cases
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun l ->
                                          fun _default_0 ->
                                            fun e ->
                                              fun _default_1 ->
                                                Exp.match_ ~loc:_loc e l))))))
                (List.cons
                   (Earley_core.Earley.fsequence try_kw
                      (Earley_core.Earley.fsequence expression
                         (Earley_core.Earley.fsequence with_kw
                            (Earley_core.Earley.fsequence match_cases
                               (Earley_core.Earley.empty_pos
                                  (fun __loc__start__buf ->
                                     fun __loc__start__pos ->
                                       fun __loc__end__buf ->
                                         fun __loc__end__pos ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           fun l ->
                                             fun _default_0 ->
                                               fun e ->
                                                 fun _default_1 ->
                                                   Exp.try_ ~loc:_loc e l))))))
                   [])))))
let (right_expression, right_expression__set__grammar) =
  Earley_core.Earley.grammar_prio "right_expression"
let _ =
  right_expression__set__grammar
    ((List.cons
        ((fun lvl -> lvl <= Dash),
          (Earley_core.Earley.fsequence (expression_lvl (NoMatch, Dash))
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.char '#' '#')
                (Earley_core.Earley.fsequence method_name
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun f -> fun e' -> Exp.send ~loc:_loc e' f))))))
        (List.cons
           ((fun lvl -> lvl <= Atom),
             (Earley_core.Earley.fsequence_position value_path
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun str1 ->
                              fun pos1 ->
                                fun str2 ->
                                  fun pos2 ->
                                    fun id ->
                                      let _loc_id =
                                        locate str1 pos1 str2 pos2 in
                                      Exp.ident ~loc:_loc (id_loc id _loc_id)))))
           (List.cons
              ((fun lvl -> lvl <= Atom),
                (Earley_core.Earley.fsequence constant
                   (Earley_core.Earley.empty_pos
                      (fun __loc__start__buf ->
                         fun __loc__start__pos ->
                           fun __loc__end__buf ->
                             fun __loc__end__pos ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos in
                               fun c -> Exp.constant ~loc:_loc c))))
              (List.cons
                 ((fun lvl -> lvl <= Atom),
                   (Earley_core.Earley.fsequence_position module_path
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '.' '.')
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char '(' '(')
                            (Earley_core.Earley.fsequence expression
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ')' ')')
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun e ->
                                                fun str1 ->
                                                  fun pos1 ->
                                                    fun str2 ->
                                                      fun pos2 ->
                                                        fun mp ->
                                                          let _loc_mp =
                                                            locate str1 pos1
                                                              str2 pos2 in
                                                          let mp =
                                                            id_loc mp _loc_mp in
                                                          Exp.open_ ~loc:_loc
                                                            (Opn.mk
                                                               ~override:Fresh
                                                               (Mod.ident mp))
                                                            e))))))))
                 (List.cons
                    ((fun lvl -> lvl <= Atom),
                      (Earley_core.Earley.fsequence_position module_path
                         (Earley_core.Earley.fsequence_ignore
                            (Earley_core.Earley.char '.' '.')
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '[' '[')
                               (Earley_core.Earley.fsequence expression_list
                                  (Earley_core.Earley.fsequence_position
                                     (Earley_core.Earley.char ']' ']')
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun str1 ->
                                                   fun pos1 ->
                                                     fun str2 ->
                                                       fun pos2 ->
                                                         fun cl ->
                                                           let _loc_cl =
                                                             locate str1 pos1
                                                               str2 pos2 in
                                                           fun l ->
                                                             fun str1 ->
                                                               fun pos1 ->
                                                                 fun str2 ->
                                                                   fun pos2
                                                                    ->
                                                                    fun mp ->
                                                                    let _loc_mp
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    let mp =
                                                                    id_loc mp
                                                                    _loc_mp in
                                                                    Exp.open_
                                                                    ~loc:_loc
                                                                    (Opn.mk
                                                                    ~override:Fresh
                                                                    (Mod.ident
                                                                    mp))
                                                                    (pexp_list
                                                                    _loc
                                                                    ~loc_cl:_loc_cl
                                                                    l)))))))))
                    (List.cons
                       ((fun lvl -> lvl <= Atom),
                         (Earley_core.Earley.fsequence_position module_path
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '.' '.')
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char '{' '{')
                                  (Earley_core.Earley.fsequence
                                     (Earley_core.Earley.option None
                                        (Earley_core.Earley.apply
                                           (fun x -> Some x)
                                           (Earley_core.Earley.fsequence
                                              expression
                                              (Earley_core.Earley.fsequence_ignore
                                                 with_kw
                                                 (Earley_core.Earley.empty
                                                    (fun _default_0 ->
                                                       _default_0))))))
                                     (Earley_core.Earley.fsequence
                                        record_list
                                        (Earley_core.Earley.fsequence_ignore
                                           (Earley_core.Earley.char '}' '}')
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun l ->
                                                         fun e ->
                                                           fun str1 ->
                                                             fun pos1 ->
                                                               fun str2 ->
                                                                 fun pos2 ->
                                                                   fun mp ->
                                                                    let _loc_mp
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    let mp =
                                                                    id_loc mp
                                                                    _loc_mp in
                                                                    Exp.open_
                                                                    ~loc:_loc
                                                                    (Opn.mk
                                                                    ~override:Fresh
                                                                    (Mod.ident
                                                                    mp))
                                                                    (Exp.record
                                                                    ~loc:_loc
                                                                    l e))))))))))
                       (List.cons
                          ((fun lvl -> lvl <= Atom),
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '(' '(')
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.option None
                                     (Earley_core.Earley.apply
                                        (fun x -> Some x) expression))
                                  (Earley_core.Earley.fsequence_ignore
                                     (Earley_core.Earley.char ')' ')')
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun e ->
                                                   match e with
                                                   | Some e ->
                                                       Exp.mk ~loc:_loc
                                                         e.pexp_desc
                                                   | None ->
                                                       let cunit =
                                                         id_loc (Lident "()")
                                                           _loc in
                                                       Exp.construct
                                                         ~loc:_loc cunit None))))))
                          (List.cons
                             ((fun lvl -> lvl <= Atom),
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char '(' '(')
                                  (Earley_core.Earley.fsequence no_parser
                                     (Earley_core.Earley.fsequence expression
                                        (Earley_core.Earley.fsequence
                                           type_coercion
                                           (Earley_core.Earley.fsequence_ignore
                                              (Earley_core.Earley.char ')'
                                                 ')')
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun t ->
                                                            fun e ->
                                                              fun _default_0
                                                                ->
                                                                match t with
                                                                | (Some t1,
                                                                   None) ->
                                                                    Exp.constraint_
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc) e
                                                                    t1
                                                                | (t1, Some
                                                                   t2) ->
                                                                    Exp.coerce
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc) e
                                                                    t1 t2
                                                                | (None,
                                                                   None) ->
                                                                    assert
                                                                    false))))))))
                             (List.cons
                                ((fun lvl -> lvl <= Atom),
                                  (Earley_core.Earley.fsequence begin_kw
                                     (Earley_core.Earley.fsequence
                                        (Earley_core.Earley.option None
                                           (Earley_core.Earley.apply
                                              (fun x -> Some x) expression))
                                        (Earley_core.Earley.fsequence end_kw
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun _default_0 ->
                                                         fun e ->
                                                           fun _default_1 ->
                                                             match e with
                                                             | Some e ->
                                                                 Exp.mk
                                                                   ~loc:_loc
                                                                   e.pexp_desc
                                                             | None ->
                                                                 let cunit =
                                                                   id_loc
                                                                    (Lident
                                                                    "()")
                                                                    _loc in
                                                                 Exp.construct
                                                                   ~loc:_loc
                                                                   cunit None))))))
                                (List.cons
                                   ((fun lvl -> lvl <= App),
                                     (Earley_core.Earley.fsequence
                                        (expression_lvl
                                           (NoMatch, (next_exp App)))
                                        (Earley_core.Earley.fsequence
                                           (Earley_core.Earley.apply
                                              (fun f -> f [])
                                              (Earley_core.Earley.fixpoint1'
                                                 (fun l -> l) argument
                                                 (fun x ->
                                                    fun f ->
                                                      fun l ->
                                                        f (List.cons x l))))
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun l ->
                                                         fun f ->
                                                           match ((f.pexp_desc),
                                                                   l)
                                                           with
                                                           | (Pexp_construct
                                                              (c, None),
                                                              (Nolabel, a)::[])
                                                               ->
                                                               Exp.construct
                                                                 ~loc:_loc c
                                                                 (Some a)
                                                           | (Pexp_variant
                                                              (c, None),
                                                              (Nolabel, a)::[])
                                                               ->
                                                               Exp.variant
                                                                 ~loc:_loc c
                                                                 (Some a)
                                                           | _ ->
                                                               Exp.apply
                                                                 ~loc:_loc f
                                                                 l)))))
                                   (List.cons
                                      ((fun lvl -> lvl <= Atom),
                                        (Earley_core.Earley.fsequence_position
                                           constructor
                                           (Earley_core.Earley.fsequence
                                              no_dot
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun _default_0 ->
                                                            fun str1 ->
                                                              fun pos1 ->
                                                                fun str2 ->
                                                                  fun pos2 ->
                                                                    fun c ->
                                                                    let _loc_c
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    Exp.construct
                                                                    ~loc:_loc
                                                                    (id_loc c
                                                                    _loc_c)
                                                                    None)))))
                                      (List.cons
                                         ((fun lvl -> lvl <= Atom),
                                           (Earley_core.Earley.fsequence
                                              tag_name
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun l ->
                                                            Exp.variant
                                                              ~loc:_loc l
                                                              None))))
                                         (List.cons
                                            ((fun lvl -> lvl <= Atom),
                                              (Earley_core.Earley.fsequence_ignore
                                                 (Earley_core.Earley.string
                                                    "[|" "[|")
                                                 (Earley_core.Earley.fsequence
                                                    expression_list
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.string
                                                          "|]" "|]")
                                                       (Earley_core.Earley.empty_pos
                                                          (fun
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
                                                                   fun l ->
                                                                    Exp.array
                                                                    ~loc:_loc
                                                                    (List.map
                                                                    fst l)))))))
                                            (List.cons
                                               ((fun lvl -> lvl <= Atom),
                                                 (Earley_core.Earley.fsequence_ignore
                                                    (Earley_core.Earley.char
                                                       '[' '[')
                                                    (Earley_core.Earley.fsequence
                                                       expression_list
                                                       (Earley_core.Earley.fsequence_position
                                                          (Earley_core.Earley.char
                                                             ']' ']')
                                                          (Earley_core.Earley.empty_pos
                                                             (fun
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
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun cl ->
                                                                    let _loc_cl
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun l ->
                                                                    Exp.mk
                                                                    ~loc:_loc
                                                                    (pexp_list
                                                                    _loc
                                                                    ~loc_cl:_loc_cl
                                                                    l).pexp_desc))))))
                                               (List.cons
                                                  ((fun lvl -> lvl <= Atom),
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.char
                                                          '{' '{')
                                                       (Earley_core.Earley.fsequence
                                                          (Earley_core.Earley.option
                                                             None
                                                             (Earley_core.Earley.apply
                                                                (fun x ->
                                                                   Some x)
                                                                (Earley_core.Earley.fsequence
                                                                   expression
                                                                   (Earley_core.Earley.fsequence_ignore
                                                                    with_kw
                                                                    (Earley_core.Earley.empty
                                                                    (fun
                                                                    _default_0
                                                                    ->
                                                                    _default_0))))))
                                                          (Earley_core.Earley.fsequence
                                                             record_list
                                                             (Earley_core.Earley.fsequence_ignore
                                                                (Earley_core.Earley.char
                                                                   '}' '}')
                                                                (Earley_core.Earley.empty_pos
                                                                   (fun
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
                                                                    fun l ->
                                                                    fun e ->
                                                                    Exp.record
                                                                    ~loc:_loc
                                                                    l e)))))))
                                                  (List.cons
                                                     ((fun lvl -> lvl <= Atom),
                                                       (Earley_core.Earley.fsequence
                                                          while_kw
                                                          (Earley_core.Earley.fsequence
                                                             expression
                                                             (Earley_core.Earley.fsequence
                                                                do_kw
                                                                (Earley_core.Earley.fsequence
                                                                   expression
                                                                   (Earley_core.Earley.fsequence
                                                                    done_kw
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun e' ->
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    fun e ->
                                                                    fun
                                                                    _default_2
                                                                    ->
                                                                    Exp.while_
                                                                    ~loc:_loc
                                                                    e e'))))))))
                                                     (List.cons
                                                        ((fun lvl ->
                                                            lvl <= Atom),
                                                          (Earley_core.Earley.fsequence
                                                             for_kw
                                                             (Earley_core.Earley.fsequence
                                                                pattern
                                                                (Earley_core.Earley.fsequence_ignore
                                                                   (Earley_core.Earley.char
                                                                    '=' '=')
                                                                   (Earley_core.Earley.fsequence
                                                                    expression
                                                                    (Earley_core.Earley.fsequence
                                                                    downto_flag
                                                                    (Earley_core.Earley.fsequence
                                                                    expression
                                                                    (Earley_core.Earley.fsequence
                                                                    do_kw
                                                                    (Earley_core.Earley.fsequence
                                                                    expression
                                                                    (Earley_core.Earley.fsequence
                                                                    done_kw
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun e''
                                                                    ->
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    fun e' ->
                                                                    fun d ->
                                                                    fun e ->
                                                                    fun id ->
                                                                    fun
                                                                    _default_2
                                                                    ->
                                                                    Exp.for_
                                                                    ~loc:_loc
                                                                    id e e' d
                                                                    e''))))))))))))
                                                        (List.cons
                                                           ((fun lvl ->
                                                               lvl <= Atom),
                                                             (Earley_core.Earley.fsequence
                                                                new_kw
                                                                (Earley_core.Earley.fsequence_position
                                                                   class_path
                                                                   (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun p ->
                                                                    let _loc_p
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    Exp.new_
                                                                    ~loc:_loc
                                                                    (id_loc p
                                                                    _loc_p))))))
                                                           (List.cons
                                                              ((fun lvl ->
                                                                  lvl <= Atom),
                                                                (Earley_core.Earley.fsequence
                                                                   object_kw
                                                                   (Earley_core.Earley.fsequence
                                                                    class_body
                                                                    (Earley_core.Earley.fsequence
                                                                    end_kw
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun o ->
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    Exp.object_
                                                                    ~loc:_loc
                                                                    o))))))
                                                              (List.cons
                                                                 ((fun lvl ->
                                                                    lvl <=
                                                                    Atom),
                                                                   (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "{<" "{<")
                                                                    (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.option
                                                                    []
                                                                    (Earley_core.Earley.fsequence
                                                                    obj_item
                                                                    (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.apply
                                                                    (fun f ->
                                                                    f [])
                                                                    (Earley_core.Earley.fixpoint'
                                                                    (fun l ->
                                                                    l)
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    semi_col
                                                                    (Earley_core.Earley.fsequence
                                                                    obj_item
                                                                    (Earley_core.Earley.empty
                                                                    (fun o ->
                                                                    o))))
                                                                    (fun x ->
                                                                    fun f ->
                                                                    fun l ->
                                                                    f
                                                                    (List.cons
                                                                    x l))))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    semi_col))
                                                                    (Earley_core.Earley.empty
                                                                    (fun l ->
                                                                    fun o ->
                                                                    o :: l))))))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    ">}" ">}")
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun l ->
                                                                    Exp.override
                                                                    ~loc:_loc
                                                                    l))))))
                                                                 (List.cons
                                                                    ((fun lvl
                                                                    ->
                                                                    lvl <=
                                                                    Atom),
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '(' '(')
                                                                    (Earley_core.Earley.fsequence
                                                                    module_kw
                                                                    (Earley_core.Earley.fsequence
                                                                    module_expr
                                                                    (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    ":" ":")
                                                                    (Earley_core.Earley.fsequence
                                                                    package_type
                                                                    (Earley_core.Earley.empty
                                                                    (fun pt
                                                                    -> pt))))))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ')' ')')
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun pt ->
                                                                    fun me ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    match pt
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    Exp.pack
                                                                    ~loc:_loc
                                                                    me
                                                                    | 
                                                                    Some pt
                                                                    ->
                                                                    let me =
                                                                    Exp.pack
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc) me in
                                                                    let pt =
                                                                    Typ.mk
                                                                    ~loc:(
                                                                    ghost
                                                                    _loc)
                                                                    pt.ptyp_desc in
                                                                    Exp.constraint_
                                                                    ~loc:_loc
                                                                    me pt))))))))
                                                                    (
                                                                    List.cons
                                                                    ((fun lvl
                                                                    ->
                                                                    lvl <=
                                                                    Dot),
                                                                    (Earley_core.Earley.fsequence
                                                                    (expression_lvl
                                                                    (NoMatch,
                                                                    Dot))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '.' '.')
                                                                    (Earley_core.Earley.fsequence
                                                                    (Earley_core.Earley.alternatives
                                                                    (List.cons
                                                                    (Earley_core.Earley.fsequence_position
                                                                    field
                                                                    (Earley_core.Earley.empty
                                                                    (fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun f ->
                                                                    let _loc_f
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun e' ->
                                                                    fun loc
                                                                    ->
                                                                    Exp.field
                                                                    ~loc e'
                                                                    (id_loc f
                                                                    _loc_f))))
                                                                    (List.cons
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "(" "(")
                                                                    (Earley_core.Earley.fsequence
                                                                    expression
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    ")" ")")
                                                                    (Earley_core.Earley.empty
                                                                    (fun f ->
                                                                    fun e' ->
                                                                    fun _l ->
                                                                    exp_apply
                                                                    _l
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _l))
                                                                    "Array"
                                                                    "get")
                                                                    [e'; f])))))
                                                                    (List.cons
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "[" "[")
                                                                    (Earley_core.Earley.fsequence
                                                                    expression
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "]" "]")
                                                                    (Earley_core.Earley.empty
                                                                    (fun f ->
                                                                    fun e' ->
                                                                    fun _l ->
                                                                    exp_apply
                                                                    _l
                                                                    (array_function
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _l))
                                                                    "String"
                                                                    "get")
                                                                    [e'; f])))))
                                                                    (List.cons
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "{" "{")
                                                                    (Earley_core.Earley.fsequence
                                                                    expression
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.string
                                                                    "}" "}")
                                                                    (Earley_core.Earley.empty
                                                                    (fun f ->
                                                                    fun e' ->
                                                                    fun _l ->
                                                                    bigarray_get
                                                                    (ghost
                                                                    (merge2
                                                                    e'.pexp_loc
                                                                    _l)) e' f)))))
                                                                    [])))))
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun r ->
                                                                    fun e' ->
                                                                    r e' _loc))))))
                                                                    [])))))))))))))))))))))),
      (fun lvl -> []))
let (semicol, semicol__set__grammar) =
  Earley_core.Earley.grammar_prio "semicol"
let _ =
  semicol__set__grammar
    ((List.cons
        ((fun (alm, lvl) -> lvl > Seq),
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty false)))
        (List.cons
           ((fun (alm, lvl) -> lvl = Seq),
             (Earley_core.Earley.fsequence semi_col
                (Earley_core.Earley.empty (fun _default_0 -> true))))
           (List.cons
              ((fun (alm, lvl) -> lvl = Seq),
                (Earley_core.Earley.fsequence no_semi
                   (Earley_core.Earley.empty (fun _default_0 -> false)))) []))),
      (fun (alm, lvl) -> []))
let (noelse, noelse__set__grammar) = Earley_core.Earley.grammar_prio "noelse"
let _ =
  noelse__set__grammar
    ((List.cons
        ((fun b -> not b),
          (Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
             (Earley_core.Earley.empty ())))
        (List.cons ((fun b -> b), no_else) [])), (fun b -> []))
let (debut, debut__set__grammar) = Earley_core.Earley.grammar_family "debut"
let debut __curry__varx0 __curry__varx1 =
  debut (__curry__varx0, __curry__varx1)
let _ =
  debut__set__grammar
    (fun (lvl, alm) ->
       Earley_core.Earley.fsequence_position (left_expr (alm, lvl))
         (Earley_core.Earley.empty
            (fun str1 ->
               fun pos1 ->
                 fun str2 ->
                   fun pos2 ->
                     fun s ->
                       let _loc_s = locate str1 pos1 str2 pos2 in
                       let (lvl0, no_else, f) = s in
                       ((lvl0, no_else), (f, _loc_s)))))
let (suit, suit__set__grammar) = Earley_core.Earley.grammar_family "suit"
let suit __curry__varx0 __curry__varx1 __curry__varx2 =
  suit (__curry__varx0, __curry__varx1, __curry__varx2)
let _ =
  suit__set__grammar
    (fun (lvl, alm, (lvl0, no_else)) ->
       Earley_core.Earley.fsequence_position (expression_lvl (alm, lvl0))
         (Earley_core.Earley.fsequence_position (semicol (alm, lvl))
            (Earley_core.Earley.fsequence (noelse no_else)
               (Earley_core.Earley.empty
                  (fun _default_0 ->
                     fun str1 ->
                       fun pos1 ->
                         fun str2 ->
                           fun pos2 ->
                             fun c ->
                               let _loc_c = locate str1 pos1 str2 pos2 in
                               fun str1 ->
                                 fun pos1 ->
                                   fun str2 ->
                                     fun pos2 ->
                                       fun e ->
                                         let _loc_e =
                                           locate str1 pos1 str2 pos2 in
                                         fun (f, _loc_s) ->
                                           let _l = merge2 _loc_s _loc_e in
                                           let _loc_c =
                                             if c then _loc_c else _loc_e in
                                           f e (_l, _loc_c))))))
let _ =
  set_expression_lvl
    (fun (alm, lvl) ->
       Earley_core.Earley.alternatives
         (List.append
            (if allow_match alm
             then
               List.cons
                 (Earley_core.Earley.fsequence prefix_expression
                    (Earley_core.Earley.fsequence (semicol (alm, lvl))
                       (Earley_core.Earley.empty
                          (fun _default_0 -> fun r -> r)))) []
             else [])
            (List.cons
               (Earley.dependent_sequence (debut lvl alm) (suit lvl alm))
               (List.cons
                  (Earley_core.Earley.fsequence (right_expression lvl)
                     (Earley_core.Earley.fsequence (semicol (alm, lvl))
                        (Earley_core.Earley.empty
                           (fun _default_0 -> fun r -> r)))) []))))
let module_expr_base = Earley_core.Earley.declare_grammar "module_expr_base"
let _ =
  Earley_core.Earley.set_grammar module_expr_base
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '(' '(')
             (Earley_core.Earley.fsequence val_kw
                (Earley_core.Earley.fsequence expression
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.option None
                         (Earley_core.Earley.apply (fun x -> Some x)
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.string ":" ":")
                               (Earley_core.Earley.fsequence package_type
                                  (Earley_core.Earley.empty (fun pt -> pt))))))
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char ')' ')')
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun pt ->
                                       fun e ->
                                         fun _default_0 ->
                                           let e =
                                             match pt with
                                             | None -> e
                                             | Some pt ->
                                                 Exp.constraint_
                                                   ~loc:(ghost _loc) e pt in
                                           Mod.unpack ~loc:_loc e)))))))
          (List.cons
             (Earley_core.Earley.fsequence module_path
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun mp -> Mod.ident ~loc:_loc (id_loc mp _loc))))
             (List.cons
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.fsequence struct_kw
                      (Earley_core.Earley.empty
                         (fun _default_0 -> push_comments ())))
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.fsequence structure
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun ms -> ms @ (attach_str _loc))))
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.fsequence end_kw
                            (Earley_core.Earley.empty
                               (fun _default_0 -> pop_comments ())))
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun _default_0 ->
                                       fun ms ->
                                         fun _default_1 ->
                                           Mod.structure ~loc:_loc ms)))))
                (List.cons
                   (Earley_core.Earley.fsequence functor_kw
                      (Earley_core.Earley.fsequence functor_parameter
                         (Earley_core.Earley.fsequence arrow_re
                            (Earley_core.Earley.fsequence module_expr
                               (Earley_core.Earley.empty_pos
                                  (fun __loc__start__buf ->
                                     fun __loc__start__pos ->
                                       fun __loc__end__buf ->
                                         fun __loc__end__pos ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           fun me ->
                                             fun _default_0 ->
                                               fun p ->
                                                 fun _default_1 ->
                                                   Mod.functor_ ~loc:_loc
                                                     (snd p) me))))))
                   (List.cons
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '(' '(')
                         (Earley_core.Earley.fsequence module_expr
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.option None
                                  (Earley_core.Earley.apply (fun x -> Some x)
                                     (Earley_core.Earley.fsequence_ignore
                                        (Earley_core.Earley.char ':' ':')
                                        (Earley_core.Earley.fsequence
                                           module_type
                                           (Earley_core.Earley.empty
                                              (fun mt -> mt))))))
                               (Earley_core.Earley.fsequence_ignore
                                  (Earley_core.Earley.char ')' ')')
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun mt ->
                                                fun me ->
                                                  match mt with
                                                  | None -> me
                                                  | Some mt ->
                                                      Mod.constraint_
                                                        ~loc:_loc me mt))))))
                      []))))))
let _ =
  set_grammar module_expr
    (Earley_core.Earley.fsequence_position module_expr_base
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l)
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "(" "(")
                   (Earley_core.Earley.fsequence module_expr
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.string ")" ")")
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun m -> (_loc, m))))))
                (fun x -> fun f -> fun l -> f (List.cons x l))))
          (Earley_core.Earley.empty
             (fun l ->
                fun str1 ->
                  fun pos1 ->
                    fun str2 ->
                      fun pos2 ->
                        fun m ->
                          let _loc_m = locate str1 pos1 str2 pos2 in
                          List.fold_left
                            (fun acc ->
                               fun (_loc_n, n) ->
                                 Mod.apply ~loc:(merge2 _loc_m _loc_n) acc n)
                            m l))))
let module_type_base = Earley_core.Earley.declare_grammar "module_type_base"
let _ =
  Earley_core.Earley.set_grammar module_type_base
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence module_kw
             (Earley_core.Earley.fsequence type_kw
                (Earley_core.Earley.fsequence of_kw
                   (Earley_core.Earley.fsequence module_expr
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun me ->
                                    fun _default_0 ->
                                      fun _default_1 ->
                                        fun _default_2 ->
                                          Mty.typeof_ ~loc:_loc me))))))
          (List.cons
             (Earley_core.Earley.fsequence modtype_path
                (Earley_core.Earley.empty_pos
                   (fun __loc__start__buf ->
                      fun __loc__start__pos ->
                        fun __loc__end__buf ->
                          fun __loc__end__pos ->
                            let _loc =
                              locate __loc__start__buf __loc__start__pos
                                __loc__end__buf __loc__end__pos in
                            fun mp -> Mty.ident ~loc:_loc (id_loc mp _loc))))
             (List.cons
                (Earley_core.Earley.fsequence
                   (Earley_core.Earley.fsequence sig_kw
                      (Earley_core.Earley.empty
                         (fun _default_0 -> push_comments ())))
                   (Earley_core.Earley.fsequence
                      (Earley_core.Earley.fsequence signature
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun ms -> ms @ (attach_sig _loc))))
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.fsequence end_kw
                            (Earley_core.Earley.empty
                               (fun _default_0 -> pop_comments ())))
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun _default_0 ->
                                       fun ms ->
                                         fun _default_1 ->
                                           Mty.signature ~loc:_loc ms)))))
                (List.cons
                   (Earley_core.Earley.fsequence functor_kw
                      (Earley_core.Earley.fsequence functor_parameter
                         (Earley_core.Earley.fsequence arrow_re
                            (Earley_core.Earley.fsequence module_type
                               (Earley_core.Earley.fsequence no_with
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun _default_0 ->
                                                fun me ->
                                                  fun _default_1 ->
                                                    fun p ->
                                                      fun _default_2 ->
                                                        Mty.functor_
                                                          ~loc:_loc (
                                                          snd p) me)))))))
                   (List.cons
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '(' '(')
                         (Earley_core.Earley.fsequence module_type
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char ')' ')')
                               (Earley_core.Earley.empty (fun mt -> mt)))))
                      []))))))
let mod_constraint = Earley_core.Earley.declare_grammar "mod_constraint"
let _ =
  Earley_core.Earley.set_grammar mod_constraint
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence module_kw
             (Earley_core.Earley.fsequence_position module_path
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string ":=" ":=")
                   (Earley_core.Earley.fsequence_position
                      extended_module_path
                      (Earley_core.Earley.empty
                         (fun str1 ->
                            fun pos1 ->
                              fun str2 ->
                                fun pos2 ->
                                  fun emp ->
                                    let _loc_emp = locate str1 pos1 str2 pos2 in
                                    fun str1 ->
                                      fun pos1 ->
                                        fun str2 ->
                                          fun pos2 ->
                                            fun mn ->
                                              let _loc_mn =
                                                locate str1 pos1 str2 pos2 in
                                              fun _default_0 ->
                                                let mn = id_loc mn _loc_mn in
                                                Pwith_modsubst
                                                  (mn, (id_loc emp _loc_emp))))))))
          (List.cons
             (Earley_core.Earley.fsequence_position type_kw
                (Earley_core.Earley.fsequence typedef_in_constraint
                   (Earley_core.Earley.empty
                      (fun tf ->
                         fun str1 ->
                           fun pos1 ->
                             fun str2 ->
                               fun pos2 ->
                                 fun t ->
                                   let _loc_t = locate str1 pos1 str2 pos2 in
                                   let (tn, ty) = tf (Some _loc_t) in
                                   Pwith_type (tn, ty)))))
             (List.cons
                (Earley_core.Earley.fsequence module_kw
                   (Earley_core.Earley.fsequence_position module_path
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char '=' '=')
                         (Earley_core.Earley.fsequence_position
                            extended_module_path
                            (Earley_core.Earley.empty
                               (fun str1 ->
                                  fun pos1 ->
                                    fun str2 ->
                                      fun pos2 ->
                                        fun m2 ->
                                          let _loc_m2 =
                                            locate str1 pos1 str2 pos2 in
                                          fun str1 ->
                                            fun pos1 ->
                                              fun str2 ->
                                                fun pos2 ->
                                                  fun m1 ->
                                                    let _loc_m1 =
                                                      locate str1 pos1 str2
                                                        pos2 in
                                                    fun _default_0 ->
                                                      let name =
                                                        id_loc m1 _loc_m1 in
                                                      Pwith_module
                                                        (name,
                                                          (id_loc m2 _loc_m2))))))))
                (List.cons
                   (Earley_core.Earley.fsequence type_kw
                      (Earley_core.Earley.fsequence type_params
                         (Earley_core.Earley.fsequence_position typeconstr
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.string ":=" ":=")
                               (Earley_core.Earley.fsequence typexpr
                                  (Earley_core.Earley.empty_pos
                                     (fun __loc__start__buf ->
                                        fun __loc__start__pos ->
                                          fun __loc__end__buf ->
                                            fun __loc__end__pos ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              fun te ->
                                                fun str1 ->
                                                  fun pos1 ->
                                                    fun str2 ->
                                                      fun pos2 ->
                                                        fun tcn ->
                                                          let _loc_tcn =
                                                            locate str1 pos1
                                                              str2 pos2 in
                                                          fun params ->
                                                            fun _default_0 ->
                                                              let tcn0 =
                                                                id_loc
                                                                  (Longident.last
                                                                    tcn)
                                                                  _loc_tcn in
                                                              let _tcn =
                                                                id_loc tcn
                                                                  _loc_tcn in
                                                              let td =
                                                                Type.mk
                                                                  ~loc:_loc
                                                                  ~params
                                                                  ~manifest:te
                                                                  tcn0 in
                                                              Pwith_typesubst
                                                                (_tcn, td))))))))
                   [])))))
let _ =
  set_grammar module_type
    (Earley_core.Earley.fsequence module_type_base
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.option None
             (Earley_core.Earley.apply (fun x -> Some x)
                (Earley_core.Earley.fsequence_ignore with_kw
                   (Earley_core.Earley.fsequence mod_constraint
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.apply (fun f -> f [])
                            (Earley_core.Earley.fixpoint' (fun l -> l)
                               (Earley_core.Earley.fsequence_ignore and_kw
                                  (Earley_core.Earley.fsequence
                                     mod_constraint
                                     (Earley_core.Earley.empty
                                        (fun _default_0 -> _default_0))))
                               (fun x -> fun f -> fun l -> f (List.cons x l))))
                         (Earley_core.Earley.empty (fun l -> fun m -> m :: l)))))))
          (Earley_core.Earley.empty_pos
             (fun __loc__start__buf ->
                fun __loc__start__pos ->
                  fun __loc__end__buf ->
                    fun __loc__end__pos ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      fun l ->
                        fun m ->
                          match l with
                          | None -> m
                          | Some l -> Mty.with_ ~loc:_loc m l))))
let structure_item_base =
  Earley_core.Earley.declare_grammar "structure_item_base"
let _ =
  Earley_core.Earley.set_grammar structure_item_base
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence floating_extension
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun ext -> Str.extension ~loc:_loc ext)))
          (List.cons
             (Earley_core.Earley.fsequence
                (Earley_str.regexp ~name:"let" let_re (fun group -> group 0))
                (Earley_core.Earley.fsequence rec_flag
                   (Earley_core.Earley.fsequence let_binding
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun l ->
                                    fun r ->
                                      fun _default_0 ->
                                        Str.value ~loc:_loc r l)))))
             (List.cons
                (Earley_core.Earley.fsequence external_kw
                   (Earley_core.Earley.fsequence_position value_name
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char ':' ':')
                         (Earley_core.Earley.fsequence typexpr
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '=' '=')
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.apply (fun f -> f [])
                                     (Earley_core.Earley.fixpoint1'
                                        (fun l -> l) string_litteral
                                        (fun x ->
                                           fun f ->
                                             fun l -> f (List.cons x l))))
                                  (Earley_core.Earley.fsequence
                                     post_item_attributes
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun a ->
                                                   fun prim ->
                                                     fun ty ->
                                                       fun str1 ->
                                                         fun pos1 ->
                                                           fun str2 ->
                                                             fun pos2 ->
                                                               fun n ->
                                                                 let _loc_n =
                                                                   locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                 fun
                                                                   _default_0
                                                                   ->
                                                                   if
                                                                    (List.length
                                                                    prim) > 3
                                                                   then
                                                                    give_up
                                                                    ();
                                                                   (let prim
                                                                    =
                                                                    List.map
                                                                    fst prim in
                                                                    let attrs
                                                                    =
                                                                    attach_attrib
                                                                    _loc a in
                                                                    Str.primitive
                                                                    ~loc:_loc
                                                                    (Val.mk
                                                                    ~loc:_loc
                                                                    ~attrs
                                                                    ~prim
                                                                    (id_loc n
                                                                    _loc_n)
                                                                    ty)))))))))))
                (List.cons
                   (Earley_core.Earley.fsequence type_definition
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun td -> Str.type_ ~loc:_loc Recursive td)))
                   (List.cons
                      (Earley_core.Earley.fsequence type_extension
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun te ->
                                       Str.type_extension ~loc:_loc te)))
                      (List.cons exception_definition
                         (List.cons
                            (Earley_core.Earley.fsequence_ignore module_kw
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.alternatives
                                     (List.cons
                                        (Earley_core.Earley.fsequence type_kw
                                           (Earley_core.Earley.fsequence_position
                                              modtype_name
                                              (Earley_core.Earley.fsequence
                                                 (Earley_core.Earley.option
                                                    None
                                                    (Earley_core.Earley.apply
                                                       (fun x -> Some x)
                                                       (Earley_core.Earley.fsequence_ignore
                                                          (Earley_core.Earley.string
                                                             "=" "=")
                                                          (Earley_core.Earley.fsequence
                                                             module_type
                                                             (Earley_core.Earley.empty
                                                                (fun mt -> mt))))))
                                                 (Earley_core.Earley.fsequence
                                                    post_item_attributes
                                                    (Earley_core.Earley.empty_pos
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
                                                                    __loc__end__pos in
                                                                fun a ->
                                                                  fun mt ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mn ->
                                                                    let _loc_mn
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let attrs
                                                                    =
                                                                    attach_attrib
                                                                    _loc a in
                                                                    Str.modtype
                                                                    ~loc:_loc
                                                                    (Mtd.mk
                                                                    ~loc:_loc
                                                                    ~attrs
                                                                    ?typ:mt
                                                                    (id_loc
                                                                    mn
                                                                    _loc_mn))))))))
                                        (List.cons
                                           (Earley_core.Earley.fsequence
                                              rec_kw
                                              (Earley_core.Earley.fsequence
                                                 module_name
                                                 (Earley_core.Earley.fsequence_position
                                                    (Earley_core.Earley.option
                                                       None
                                                       (Earley_core.Earley.apply
                                                          (fun x -> Some x)
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.char
                                                                ':' ':')
                                                             (Earley_core.Earley.fsequence
                                                                module_type
                                                                (Earley_core.Earley.empty
                                                                   (fun mt ->
                                                                    mt))))))
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.char
                                                          '=' '=')
                                                       (Earley_core.Earley.fsequence_position
                                                          module_expr
                                                          (Earley_core.Earley.fsequence
                                                             (Earley_core.Earley.apply
                                                                (fun f ->
                                                                   f [])
                                                                (Earley_core.Earley.fixpoint'
                                                                   (fun l ->
                                                                    l)
                                                                   (Earley_core.Earley.fsequence
                                                                    and_kw
                                                                    (Earley_core.Earley.fsequence
                                                                    module_name
                                                                    (Earley_core.Earley.fsequence_position
                                                                    (Earley_core.Earley.option
                                                                    None
                                                                    (Earley_core.Earley.apply
                                                                    (fun x ->
                                                                    Some x)
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    ':' ':')
                                                                    (Earley_core.Earley.fsequence
                                                                    module_type
                                                                    (Earley_core.Earley.empty
                                                                    (fun mt
                                                                    -> mt))))))
                                                                    (Earley_core.Earley.fsequence_ignore
                                                                    (Earley_core.Earley.char
                                                                    '=' '=')
                                                                    (Earley_core.Earley.fsequence_position
                                                                    module_expr
                                                                    (Earley_core.Earley.empty
                                                                    (fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun me ->
                                                                    let _loc_me
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mt ->
                                                                    let _loc_mt
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun mn ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let loc =
                                                                    merge2
                                                                    _loc_mt
                                                                    _loc_me in
                                                                    let me =
                                                                    match mt
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    me
                                                                    | 
                                                                    Some mt
                                                                    ->
                                                                    Mod.constraint_
                                                                    ~loc me
                                                                    mt in
                                                                    Mb.mk
                                                                    ~loc mn
                                                                    me)))))))
                                                                   (fun x ->
                                                                    fun f ->
                                                                    fun l ->
                                                                    f
                                                                    (List.cons
                                                                    x l))))
                                                             (Earley_core.Earley.empty_pos
                                                                (fun
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
                                                                    fun ms ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun me ->
                                                                    let _loc_me
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mt ->
                                                                    let _loc_mt
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun mn ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let loc =
                                                                    merge2
                                                                    _loc_mt
                                                                    _loc_me in
                                                                    let me =
                                                                    match mt
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    me
                                                                    | 
                                                                    Some mt
                                                                    ->
                                                                    Mod.constraint_
                                                                    ~loc me
                                                                    mt in
                                                                    Str.rec_module
                                                                    ~loc:_loc
                                                                    ((Mb.mk
                                                                    ~loc mn
                                                                    me) ::
                                                                    ms)))))))))
                                           (List.cons
                                              (Earley_core.Earley.fsequence
                                                 module_name
                                                 (Earley_core.Earley.fsequence
                                                    (Earley_core.Earley.apply
                                                       (fun f -> f [])
                                                       (Earley_core.Earley.fixpoint'
                                                          (fun l -> l)
                                                          functor_parameter
                                                          (fun x ->
                                                             fun f ->
                                                               fun l ->
                                                                 f
                                                                   (List.cons
                                                                    x l))))
                                                    (Earley_core.Earley.fsequence_position
                                                       (Earley_core.Earley.option
                                                          None
                                                          (Earley_core.Earley.apply
                                                             (fun x -> Some x)
                                                             (Earley_core.Earley.fsequence_ignore
                                                                (Earley_core.Earley.char
                                                                   ':' ':')
                                                                (Earley_core.Earley.fsequence
                                                                   module_type
                                                                   (Earley_core.Earley.empty
                                                                    (fun mt
                                                                    -> mt))))))
                                                       (Earley_core.Earley.fsequence_ignore
                                                          (Earley_core.Earley.char
                                                             '=' '=')
                                                          (Earley_core.Earley.fsequence_position
                                                             module_expr
                                                             (Earley_core.Earley.empty_pos
                                                                (fun
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
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun me ->
                                                                    let _loc_me
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mt ->
                                                                    let _loc_mt
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun l ->
                                                                    fun mn ->
                                                                    let me =
                                                                    let loc =
                                                                    merge2
                                                                    _loc_mt
                                                                    _loc_me in
                                                                    match mt
                                                                    with
                                                                    | 
                                                                    None ->
                                                                    me
                                                                    | 
                                                                    Some mt
                                                                    ->
                                                                    Mod.constraint_
                                                                    ~loc me
                                                                    mt in
                                                                    let fn
                                                                    acc
                                                                    (loc, p)
                                                                    =
                                                                    let loc =
                                                                    merge2
                                                                    loc
                                                                    _loc_me in
                                                                    Mod.functor_
                                                                    ~loc p
                                                                    acc in
                                                                    let me =
                                                                    List.fold_left
                                                                    fn me
                                                                    (List.rev
                                                                    l) in
                                                                    Str.module_
                                                                    ~loc:_loc
                                                                    (Mb.mk
                                                                    ~loc:_loc
                                                                    mn me))))))))
                                              []))))
                                  (Earley_core.Earley.empty (fun r -> r))))
                            (List.cons
                               (Earley_core.Earley.fsequence open_kw
                                  (Earley_core.Earley.fsequence override_flag
                                     (Earley_core.Earley.fsequence
                                        module_expr
                                        (Earley_core.Earley.fsequence
                                           post_item_attributes
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun a ->
                                                         fun me ->
                                                           fun o ->
                                                             fun _default_0
                                                               ->
                                                               let attrs =
                                                                 attach_attrib
                                                                   _loc a in
                                                               Str.open_
                                                                 ~loc:_loc
                                                                 (Opn.mk
                                                                    ~loc:_loc
                                                                    ~attrs
                                                                    ~override:o
                                                                    me)))))))
                               (List.cons
                                  (Earley_core.Earley.fsequence include_kw
                                     (Earley_core.Earley.fsequence
                                        module_expr
                                        (Earley_core.Earley.fsequence
                                           post_item_attributes
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun a ->
                                                         fun me ->
                                                           fun _default_0 ->
                                                             let attrs =
                                                               attach_attrib
                                                                 _loc a in
                                                             Str.include_
                                                               ~loc:_loc
                                                               (Incl.mk
                                                                  ~loc:_loc
                                                                  ~attrs me))))))
                                  (List.cons
                                     (Earley_core.Earley.fsequence
                                        classtype_definition
                                        (Earley_core.Earley.empty_pos
                                           (fun __loc__start__buf ->
                                              fun __loc__start__pos ->
                                                fun __loc__end__buf ->
                                                  fun __loc__end__pos ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    fun ctd ->
                                                      Str.class_type
                                                        ~loc:_loc ctd)))
                                     (List.cons
                                        (Earley_core.Earley.fsequence
                                           class_definition
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun cds ->
                                                         Str.class_ ~loc:_loc
                                                           cds)))
                                        (List.cons
                                           (Earley_core.Earley.fsequence
                                              floating_attribute
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun attr ->
                                                            Str.attribute
                                                              ~loc:_loc attr)))
                                           [])))))))))))))
let structure_item_aux =
  Earley_core.Earley.declare_grammar "structure_item_aux"
let _ =
  Earley_core.Earley.set_grammar structure_item_aux
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence structure_item_aux
             (Earley_core.Earley.fsequence double_semi_col
                (Earley_core.Earley.fsequence_ignore ext_attributes
                   (Earley_core.Earley.fsequence_position expression
                      (Earley_core.Earley.empty
                         (fun str1 ->
                            fun pos1 ->
                              fun str2 ->
                                fun pos2 ->
                                  fun e ->
                                    let _loc_e = locate str1 pos1 str2 pos2 in
                                    fun _default_0 ->
                                      fun s1 -> (Str.eval ~loc:_loc_e e) ::
                                        (List.rev_append (attach_str _loc_e)
                                           s1)))))))
          (List.cons
             (Earley_core.Earley.fsequence_ignore ext_attributes
                (Earley_core.Earley.empty []))
             (List.cons
                (Earley_core.Earley.fsequence_ignore ext_attributes
                   (Earley_core.Earley.fsequence_position expression
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun str1 ->
                                    fun pos1 ->
                                      fun str2 ->
                                        fun pos2 ->
                                          fun e ->
                                            let _loc_e =
                                              locate str1 pos1 str2 pos2 in
                                            (attach_str _loc) @
                                              [Str.eval ~loc:_loc_e e]))))
                (List.cons
                   (Earley_core.Earley.fsequence structure_item_aux
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.option () double_semi_col)
                         (Earley_core.Earley.fsequence_ignore ext_attributes
                            (Earley_core.Earley.fsequence
                               (Earley_core.Earley.alternatives
                                  (List.cons
                                     (Earley_core.Earley.fsequence_position
                                        structure_item_base
                                        (Earley_core.Earley.empty
                                           (fun str1 ->
                                              fun pos1 ->
                                                fun str2 ->
                                                  fun pos2 ->
                                                    fun s2 ->
                                                      let _loc_s2 =
                                                        locate str1 pos1 str2
                                                          pos2 in
                                                      fun s1 -> s2 ::
                                                        (List.rev_append
                                                           (attach_str
                                                              _loc_s2) s1))))
                                     (List.cons
                                        (Earley_core.Earley.fsequence_position
                                           Pa_parser.extra_structure
                                           (Earley_core.Earley.empty
                                              (fun str1 ->
                                                 fun pos1 ->
                                                   fun str2 ->
                                                     fun pos2 ->
                                                       fun e ->
                                                         let _loc_e =
                                                           locate str1 pos1
                                                             str2 pos2 in
                                                         fun s1 ->
                                                           List.rev_append e
                                                             (List.rev_append
                                                                (attach_str
                                                                   _loc_e) s1))))
                                        [])))
                               (Earley_core.Earley.empty
                                  (fun f -> fun _default_0 -> fun s1 -> f s1))))))
                   [])))))
let _ =
  set_grammar structure_item
    (Earley_core.Earley.fsequence structure_item_aux
       (Earley_core.Earley.fsequence_ignore
          (Earley_core.Earley.option None
             (Earley_core.Earley.apply (fun x -> Some x) double_semi_col))
          (Earley_core.Earley.empty (fun l -> List.rev l))))
let _ =
  set_grammar structure_item_simple
    (Earley_core.Earley.apply (fun f -> f [])
       (Earley_core.Earley.fixpoint' (fun l -> l) structure_item_base
          (fun x -> fun f -> fun l -> f (List.cons x l))))
let signature_item_base =
  Earley_core.Earley.declare_grammar "signature_item_base"
let _ =
  Earley_core.Earley.set_grammar signature_item_base
    (Earley_core.Earley.alternatives
       (List.cons
          (Earley_core.Earley.fsequence floating_extension
             (Earley_core.Earley.empty_pos
                (fun __loc__start__buf ->
                   fun __loc__start__pos ->
                     fun __loc__end__buf ->
                       fun __loc__end__pos ->
                         let _loc =
                           locate __loc__start__buf __loc__start__pos
                             __loc__end__buf __loc__end__pos in
                         fun ext -> Sig.extension ~loc:_loc ext)))
          (List.cons
             (Earley_core.Earley.fsequence val_kw
                (Earley_core.Earley.fsequence_position value_name
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.char ':' ':')
                      (Earley_core.Earley.fsequence typexpr
                         (Earley_core.Earley.fsequence post_item_attributes
                            (Earley_core.Earley.empty_pos
                               (fun __loc__start__buf ->
                                  fun __loc__start__pos ->
                                    fun __loc__end__buf ->
                                      fun __loc__end__pos ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        fun a ->
                                          fun ty ->
                                            fun str1 ->
                                              fun pos1 ->
                                                fun str2 ->
                                                  fun pos2 ->
                                                    fun n ->
                                                      let _loc_n =
                                                        locate str1 pos1 str2
                                                          pos2 in
                                                      fun _default_0 ->
                                                        let attrs =
                                                          attach_attrib _loc
                                                            a in
                                                        Sig.value ~loc:_loc
                                                          (Val.mk ~loc:_loc
                                                             ~attrs
                                                             (id_loc n _loc_n)
                                                             ty))))))))
             (List.cons
                (Earley_core.Earley.fsequence external_kw
                   (Earley_core.Earley.fsequence_position value_name
                      (Earley_core.Earley.fsequence_ignore
                         (Earley_core.Earley.char ':' ':')
                         (Earley_core.Earley.fsequence typexpr
                            (Earley_core.Earley.fsequence_ignore
                               (Earley_core.Earley.char '=' '=')
                               (Earley_core.Earley.fsequence
                                  (Earley_core.Earley.apply (fun f -> f [])
                                     (Earley_core.Earley.fixpoint1'
                                        (fun l -> l) string_litteral
                                        (fun x ->
                                           fun f ->
                                             fun l -> f (List.cons x l))))
                                  (Earley_core.Earley.fsequence
                                     post_item_attributes
                                     (Earley_core.Earley.empty_pos
                                        (fun __loc__start__buf ->
                                           fun __loc__start__pos ->
                                             fun __loc__end__buf ->
                                               fun __loc__end__pos ->
                                                 let _loc =
                                                   locate __loc__start__buf
                                                     __loc__start__pos
                                                     __loc__end__buf
                                                     __loc__end__pos in
                                                 fun a ->
                                                   fun prim ->
                                                     fun ty ->
                                                       fun str1 ->
                                                         fun pos1 ->
                                                           fun str2 ->
                                                             fun pos2 ->
                                                               fun n ->
                                                                 let _loc_n =
                                                                   locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                 fun
                                                                   _default_0
                                                                   ->
                                                                   if
                                                                    (List.length
                                                                    prim) > 3
                                                                   then
                                                                    give_up
                                                                    ();
                                                                   (let prim
                                                                    =
                                                                    List.map
                                                                    fst prim in
                                                                    let attrs
                                                                    =
                                                                    attach_attrib
                                                                    _loc a in
                                                                    Sig.value
                                                                    ~loc:_loc
                                                                    (Val.mk
                                                                    ~loc:_loc
                                                                    ~attrs
                                                                    ~prim
                                                                    (id_loc n
                                                                    _loc_n)
                                                                    ty)))))))))))
                (List.cons
                   (Earley_core.Earley.fsequence type_definition
                      (Earley_core.Earley.empty_pos
                         (fun __loc__start__buf ->
                            fun __loc__start__pos ->
                              fun __loc__end__buf ->
                                fun __loc__end__pos ->
                                  let _loc =
                                    locate __loc__start__buf
                                      __loc__start__pos __loc__end__buf
                                      __loc__end__pos in
                                  fun td -> Sig.type_ ~loc:_loc Recursive td)))
                   (List.cons
                      (Earley_core.Earley.fsequence type_extension
                         (Earley_core.Earley.empty_pos
                            (fun __loc__start__buf ->
                               fun __loc__start__pos ->
                                 fun __loc__end__buf ->
                                   fun __loc__end__pos ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     fun te ->
                                       Sig.type_extension ~loc:_loc te)))
                      (List.cons
                         (Earley_core.Earley.fsequence exception_kw
                            (Earley_core.Earley.fsequence (constr_decl false)
                               (Earley_core.Earley.empty_pos
                                  (fun __loc__start__buf ->
                                     fun __loc__start__pos ->
                                       fun __loc__end__buf ->
                                         fun __loc__end__pos ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           fun
                                             ((name, args, res, a) as
                                                _default_0)
                                             ->
                                             fun _default_1 ->
                                               let cd =
                                                 Te.decl
                                                   ~attrs:(attach_attrib _loc
                                                             a) ~loc:_loc
                                                   ~args ?res name in
                                               Sig.exception_ ~loc:_loc
                                                 (Te.mk_exception ~loc:_loc
                                                    cd)))))
                         (List.cons
                            (Earley_core.Earley.fsequence module_kw
                               (Earley_core.Earley.fsequence rec_kw
                                  (Earley_core.Earley.fsequence_position
                                     module_name
                                     (Earley_core.Earley.fsequence_ignore
                                        (Earley_core.Earley.char ':' ':')
                                        (Earley_core.Earley.fsequence
                                           module_type
                                           (Earley_core.Earley.fsequence_position
                                              post_item_attributes
                                              (Earley_core.Earley.fsequence
                                                 (Earley_core.Earley.apply
                                                    (fun f -> f [])
                                                    (Earley_core.Earley.fixpoint'
                                                       (fun l -> l)
                                                       (Earley_core.Earley.fsequence
                                                          and_kw
                                                          (Earley_core.Earley.fsequence
                                                             module_name
                                                             (Earley_core.Earley.fsequence_ignore
                                                                (Earley_core.Earley.char
                                                                   ':' ':')
                                                                (Earley_core.Earley.fsequence
                                                                   module_type
                                                                   (Earley_core.Earley.fsequence
                                                                    post_item_attributes
                                                                    (Earley_core.Earley.empty_pos
                                                                    (fun
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
                                                                    fun a ->
                                                                    fun mt ->
                                                                    fun mn ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    Md.mk
                                                                    ~loc:_loc
                                                                    ~attrs:(
                                                                    attach_attrib
                                                                    _loc a)
                                                                    mn mt)))))))
                                                       (fun x ->
                                                          fun f ->
                                                            fun l ->
                                                              f
                                                                (List.cons x
                                                                   l))))
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
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
                                                             fun ms ->
                                                               fun str1 ->
                                                                 fun pos1 ->
                                                                   fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun a ->
                                                                    let _loc_a
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun mt ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mn ->
                                                                    let _loc_mn
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    fun
                                                                    _default_1
                                                                    ->
                                                                    let loc_first
                                                                    =
                                                                    merge2
                                                                    _loc_mn
                                                                    _loc_a in
                                                                    let m =
                                                                    Md.mk
                                                                    ~loc:loc_first
                                                                    ~attrs:(
                                                                    attach_attrib
                                                                    loc_first
                                                                    a) mn mt in
                                                                    Sig.rec_module
                                                                    ~loc:_loc
                                                                    (m :: ms))))))))))
                            (List.cons
                               (Earley_core.Earley.fsequence_ignore module_kw
                                  (Earley_core.Earley.fsequence
                                     (Earley_core.Earley.alternatives
                                        (List.cons
                                           (Earley_core.Earley.fsequence
                                              type_kw
                                              (Earley_core.Earley.fsequence_position
                                                 modtype_name
                                                 (Earley_core.Earley.fsequence
                                                    (Earley_core.Earley.option
                                                       None
                                                       (Earley_core.Earley.apply
                                                          (fun x -> Some x)
                                                          (Earley_core.Earley.fsequence_ignore
                                                             (Earley_core.Earley.char
                                                                '=' '=')
                                                             (Earley_core.Earley.fsequence
                                                                module_type
                                                                (Earley_core.Earley.empty
                                                                   (fun mt ->
                                                                    mt))))))
                                                    (Earley_core.Earley.fsequence
                                                       post_item_attributes
                                                       (Earley_core.Earley.empty_pos
                                                          (fun
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
                                                                   fun a ->
                                                                    fun mt ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mn ->
                                                                    let _loc_mn
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let attrs
                                                                    =
                                                                    attach_attrib
                                                                    _loc a in
                                                                    Sig.modtype
                                                                    ~loc:_loc
                                                                    (Mtd.mk
                                                                    ~loc:_loc
                                                                    ~attrs
                                                                    ?typ:mt
                                                                    (id_loc
                                                                    mn
                                                                    _loc_mn))))))))
                                           (List.cons
                                              (Earley_core.Earley.fsequence
                                                 module_name
                                                 (Earley_core.Earley.fsequence
                                                    (Earley_core.Earley.apply
                                                       (fun f -> f [])
                                                       (Earley_core.Earley.fixpoint'
                                                          (fun l -> l)
                                                          functor_parameter
                                                          (fun x ->
                                                             fun f ->
                                                               fun l ->
                                                                 f
                                                                   (List.cons
                                                                    x l))))
                                                    (Earley_core.Earley.fsequence_ignore
                                                       (Earley_core.Earley.char
                                                          ':' ':')
                                                       (Earley_core.Earley.fsequence_position
                                                          module_type
                                                          (Earley_core.Earley.fsequence
                                                             post_item_attributes
                                                             (Earley_core.Earley.empty_pos
                                                                (fun
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
                                                                    fun a ->
                                                                    fun str1
                                                                    ->
                                                                    fun pos1
                                                                    ->
                                                                    fun str2
                                                                    ->
                                                                    fun pos2
                                                                    ->
                                                                    fun mt ->
                                                                    let _loc_mt
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun l ->
                                                                    fun mn ->
                                                                    let fn
                                                                    acc
                                                                    (loc, p)
                                                                    =
                                                                    let loc =
                                                                    merge2
                                                                    loc
                                                                    _loc_mt in
                                                                    Mty.functor_
                                                                    ~loc p
                                                                    acc in
                                                                    let mt =
                                                                    List.fold_left
                                                                    fn mt
                                                                    (List.rev
                                                                    l) in
                                                                    let attrs
                                                                    =
                                                                    attach_attrib
                                                                    _loc a in
                                                                    Sig.module_
                                                                    ~loc:_loc
                                                                    (Md.mk
                                                                    ~loc:_loc
                                                                    ~attrs mn
                                                                    mt))))))))
                                              [])))
                                     (Earley_core.Earley.empty (fun r -> r))))
                               (List.cons
                                  (Earley_core.Earley.fsequence open_kw
                                     (Earley_core.Earley.fsequence
                                        override_flag
                                        (Earley_core.Earley.fsequence_position
                                           module_path
                                           (Earley_core.Earley.fsequence
                                              post_item_attributes
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun a ->
                                                            fun str1 ->
                                                              fun pos1 ->
                                                                fun str2 ->
                                                                  fun pos2 ->
                                                                    fun m ->
                                                                    let _loc_m
                                                                    =
                                                                    locate
                                                                    str1 pos1
                                                                    str2 pos2 in
                                                                    fun o ->
                                                                    fun
                                                                    _default_0
                                                                    ->
                                                                    let attrs
                                                                    =
                                                                    attach_attrib
                                                                    _loc a in
                                                                    Sig.open_
                                                                    ~loc:_loc
                                                                    (Opn.mk
                                                                    ~loc:_loc
                                                                    ~attrs
                                                                    ~override:o
                                                                    (id_loc m
                                                                    _loc_m))))))))
                                  (List.cons
                                     (Earley_core.Earley.fsequence include_kw
                                        (Earley_core.Earley.fsequence
                                           module_type
                                           (Earley_core.Earley.fsequence
                                              post_item_attributes
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun a ->
                                                            fun me ->
                                                              fun _default_0
                                                                ->
                                                                Sig.include_
                                                                  ~loc:_loc
                                                                  (Incl.mk
                                                                    ~loc:_loc
                                                                    ~attrs:(
                                                                    attach_attrib
                                                                    _loc a)
                                                                    me))))))
                                     (List.cons
                                        (Earley_core.Earley.fsequence
                                           classtype_definition
                                           (Earley_core.Earley.empty_pos
                                              (fun __loc__start__buf ->
                                                 fun __loc__start__pos ->
                                                   fun __loc__end__buf ->
                                                     fun __loc__end__pos ->
                                                       let _loc =
                                                         locate
                                                           __loc__start__buf
                                                           __loc__start__pos
                                                           __loc__end__buf
                                                           __loc__end__pos in
                                                       fun ctd ->
                                                         Sig.class_type
                                                           ~loc:_loc ctd)))
                                        (List.cons
                                           (Earley_core.Earley.fsequence
                                              class_specification
                                              (Earley_core.Earley.empty_pos
                                                 (fun __loc__start__buf ->
                                                    fun __loc__start__pos ->
                                                      fun __loc__end__buf ->
                                                        fun __loc__end__pos
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          fun cs ->
                                                            Sig.class_
                                                              ~loc:_loc cs)))
                                           (List.cons
                                              (Earley_core.Earley.fsequence
                                                 floating_attribute
                                                 (Earley_core.Earley.empty_pos
                                                    (fun __loc__start__buf ->
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
                                                             fun attr ->
                                                               Sig.attribute
                                                                 ~loc:_loc
                                                                 attr))) []))))))))))))))
let _ =
  set_grammar signature_item
    (Earley_core.Earley.fsequence signature_item_base
       (Earley_core.Earley.fsequence_ignore
          (Earley_core.Earley.option None
             (Earley_core.Earley.apply (fun x -> Some x) double_semi_col))
          (Earley_core.Earley.empty_pos
             (fun __loc__start__buf ->
                fun __loc__start__pos ->
                  fun __loc__end__buf ->
                    fun __loc__end__pos ->
                      let _loc =
                        locate __loc__start__buf __loc__start__pos
                          __loc__end__buf __loc__end__pos in
                      fun s -> (attach_sig _loc) @ [s]))))
