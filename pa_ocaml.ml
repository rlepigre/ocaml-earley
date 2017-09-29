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
open Earley
open Charset
#ifversion >= 4.02
open Ast_helper
#endif
open Asttypes
open Parsetree
open Longident
open Pa_ast
open Pa_lexing
include Pa_ocaml_prelude

#define LOCATE locate

module Make = functor (Initial:Extension) -> struct

include Initial

let ouident = uident
let parser uident   =
  | ouident
  | "$uid:" e:expression - '$' -> Quote.string_antiquotation _loc e

let olident = lident
let parser lident   =
  | olident
  | "$lid:" e:expression - '$' -> Quote.string_antiquotation _loc e

let oident = ident
let parser ident   =
  | oident
  | "$ident:" e:expression - '$' -> Quote.string_antiquotation _loc e

(* FIXME ... !Main.a = !(Main.a) !main.a = (!main).a ... *)
#ifversion >= 4.03
let mk_unary_opp name _loc_name arg _loc_arg =
  let res =
    match name, arg.pexp_desc with
    | "-", Pexp_constant(Pconst_integer(n,o)) ->
       Pexp_constant(Pconst_integer("-"^n,o))
    | ("-" | "-."), Pexp_constant(Pconst_float(f,o)) ->
       Pexp_constant(Pconst_float("-" ^ f,o))
    | "+", Pexp_constant(Pconst_integer _)
    | ("+" | "+."), Pexp_constant(Pconst_float _) -> arg.pexp_desc
    | ("-" | "-." | "+" | "+."), _ ->
       let p = loc_expr _loc_name (Pexp_ident (id_loc (Lident ("~" ^ name)) _loc_name)) in
       Pexp_apply(p, [nolabel, arg])
    | _ ->
       let p = loc_expr _loc_name (Pexp_ident (id_loc (Lident (name)) _loc_name)) in
       Pexp_apply(p, [nolabel, arg])
  in
  loc_expr (merge2 _loc_name _loc_arg) res
#else
let mk_unary_opp name _loc_name arg _loc_arg =
  let res =
    match name, arg.pexp_desc with
    | "-", Pexp_constant(Const_int n) ->
       Pexp_constant(Const_int(-n))
    | "-", Pexp_constant(Const_int32 n) ->
       Pexp_constant(Const_int32(Int32.neg n))
    | "-", Pexp_constant(Const_int64 n) ->
       Pexp_constant(Const_int64(Int64.neg n))
    | "-", Pexp_constant(Const_nativeint n) ->
       Pexp_constant(Const_nativeint(Nativeint.neg n))
    | ("-" | "-."), Pexp_constant(Const_float f) ->
       Pexp_constant(Const_float("-" ^ f))
    | "+", Pexp_constant(Const_int _)
    | "+", Pexp_constant(Const_int32 _)
    | "+", Pexp_constant(Const_int64 _)
    | "+", Pexp_constant(Const_nativeint _)
    | ("+" | "+."), Pexp_constant(Const_float _) -> arg.pexp_desc
    | ("-" | "-." | "+" | "+."), _ ->
       let p = loc_expr _loc_name (Pexp_ident (id_loc (Lident ("~" ^ name)) _loc_name)) in
       Pexp_apply(p, ["", arg])
    | _ ->
       let p = loc_expr _loc_name (Pexp_ident (id_loc (Lident (name)) _loc_name)) in
       Pexp_apply(p, ["", arg])
  in
  loc_expr (merge2 _loc_name _loc_arg) res
#endif

let check_variable vl loc v =
  if List.mem v vl then
    raise Syntaxerr.(Error(Variable_in_scope(loc,v)))

let varify_constructors var_names t =
  let rec loop t =
    let desc =
      match t.ptyp_desc with
      | Ptyp_any -> Ptyp_any
      | Ptyp_var x ->
          check_variable var_names t.ptyp_loc x;
          Ptyp_var x
      | Ptyp_arrow (label,core_type,core_type') ->
          Ptyp_arrow(label, loop core_type, loop core_type')
      | Ptyp_tuple lst -> Ptyp_tuple (List.map loop lst)
      | Ptyp_constr( { txt = Lident s }, []) when List.mem s var_names ->
          Ptyp_var s
      | Ptyp_constr(longident, lst) ->
          Ptyp_constr(longident, List.map loop lst)
#ifversion >= 4.02
      | Ptyp_object (lst, cl) ->
          Ptyp_object (List.map loop_core_field lst, cl)
      | Ptyp_class (longident, lst) ->
          Ptyp_class (longident, List.map loop lst)
      | Ptyp_extension(_) as ty -> ty
#else
      | Ptyp_object lst ->
          Ptyp_object (List.map loop_core_field lst)
      | Ptyp_class (longident, lst, lbl_list) ->
          Ptyp_class (longident, List.map loop lst, lbl_list)
#endif
      | Ptyp_alias(core_type, string) ->
          check_variable var_names t.ptyp_loc string;
          Ptyp_alias(loop core_type, string)
      | Ptyp_variant(row_field_list, flag, lbl_lst_option) ->
          Ptyp_variant(List.map loop_row_field row_field_list,
                       flag, lbl_lst_option)
      | Ptyp_poly(string_lst, core_type) ->
#ifversion >= 4.05
          List.iter (fun v -> check_variable var_names t.ptyp_loc v.txt)
                string_lst;
#else
          List.iter (check_variable var_names t.ptyp_loc) string_lst;
#endif
          Ptyp_poly(string_lst, loop core_type)
      | Ptyp_package(longident,lst) ->
          Ptyp_package(longident,List.map (fun (n,typ) -> (n,loop typ) ) lst)
    in
    {t with ptyp_desc = desc}
#ifversion >= 4.02
  and loop_core_field (str, attr, ty) = (str, attr, loop ty)
#else
  and loop_core_field t =
    let desc =
      match t.pfield_desc with
      | Pfield(n,typ) ->
          Pfield(n,loop typ)
      | Pfield_var ->
          Pfield_var
    in
    { t with pfield_desc=desc}
#endif
  and loop_row_field  =
    function
#ifversion >= 4.02
      | Rtag(label,attr,flag,lst) ->
          Rtag(label,attr,flag,List.map loop lst)
#else
      | Rtag(label,flag,lst) ->
          Rtag(label,flag,List.map loop lst)
#endif
      | Rinherit t ->
          Rinherit (loop t)
  in
  loop t

let wrap_type_annotation _loc newtypes core_type body =
  let exp = loc_expr (ghost _loc) (pexp_constraint(body,core_type)) in
  let exp =
    List.fold_right (fun newtype exp -> loc_expr _loc (Pexp_newtype (newtype, exp)))
      newtypes exp
  in
#ifversion >= 4.05
  let newtypes0 = List.map (fun v -> v.txt) newtypes in
#else
  let newtypes0 = newtypes in
#endif
  (exp, loc_typ _loc (Ptyp_poly(newtypes,varify_constructors newtypes0 core_type)))

(* Floating-point litterals *)
let float_litteral = Earley.apply fst Pa_lexing.float_litteral
let _ = set_grammar char_litteral Pa_lexing.char_litteral
let _ = set_grammar string_litteral (Earley.apply fst Pa_lexing.string_litteral)
let _ = set_grammar regexp_litteral Pa_lexing.regexp_litteral

type tree = Node of tree * tree | Leaf of string

let string_of_tree (t:tree) : string =
  let b = Buffer.create 101 in
  let rec fn = function
      Leaf s -> Buffer.add_string b s
    | Node(a,b) -> fn a; fn b
  in
  fn t;
  Buffer.contents b

(* Naming labels *)
let label_name = lident

let parser opt_label =
  | '?' - ln:label_name no_colon -> ln (* no constructor, we add it later in this case *)

let parser ty_label =
  | '~' - s:lident ':' -> labelled s

let parser ty_opt_label =
  | '?' - s:lident ':' -> optional s

let parser maybe_opt_label =
  | o:STR("?")? ln:label_name ->
      (if o = None then labelled ln else (optional ln))

(****************************************************************************
 * Names                                                                    *
 ****************************************************************************)

(* FIXME: add antiquotations for all as done for field_name *)

let operator_name =
  alternatives (prefix_symbol Prefix :: List.map infix_symbol infix_prios)

let parser value_name =
    id:lident -> id
  | '(' op:operator_name ')' -> op

let constr_name     = uident
let parser tag_name = STR("`") c:ident -> c

let typeconstr_name = lident
let field_name      = lident

let smodule_name    = uident
let parser module_name = u:uident -> id_loc u _loc

let modtype_name    = ident
let class_name      = lident
let inst_var_name   = lident
let method_name     = lident

let module_path_gen, set_module_path_gen  = grammar_family "module_path_gen"
let module_path_suit, set_module_path_suit  = grammar_family "module_path_suit"

let parser module_path_suit_aux allow_app =
  | STR("(") m':(module_path_gen true) STR(")") when allow_app ->
      (fun a -> Lapply(a, m'))
  | STR(".") m:smodule_name ->
      (fun acc -> Ldot(acc, m))

let _ = set_module_path_suit (fun allow_app ->
    parser
      f:(module_path_suit_aux allow_app) g:(module_path_suit allow_app) -> (fun acc -> g (f acc))
    | EMPTY -> (fun acc -> acc)
    )

let _ = set_module_path_gen (fun allow_app ->
  parser
  | m:smodule_name s:(module_path_suit allow_app) -> s (Lident m)
  )

let module_path = module_path_gen false
let extended_module_path = module_path_gen true

let _ = set_grammar value_path (
  parser
  | mp:{m:module_path STR(".")}? vn:value_name ->
      (match mp with
       | None   -> Lident vn
       | Some p -> Ldot(p, vn)))

let parser constr =
  | mp:{m:module_path STR(".")}? cn:constr_name ->
      (match mp with
       | None   -> Lident cn
       | Some p -> Ldot(p, cn))

let parser typeconstr =
  | mp:{m:extended_module_path STR(".")}? tcn:typeconstr_name ->
      (match mp with
       | None   -> Lident tcn
       | Some p -> Ldot(p, tcn))

let parser field =
  | mp:{m:module_path STR(".")}? fn:field_name ->
      (match mp with
       | None   -> Lident fn
       | Some p -> Ldot(p, fn))

let parser class_path =
  | mp:{m:module_path STR(".")}? cn:class_name ->
      (match mp with
       | None   -> Lident cn
       | Some p -> Ldot(p, cn))

let parser modtype_path =
  | mp:{m:extended_module_path STR(".")}? mtn:modtype_name ->
      (match mp with
       | None   -> Lident mtn
       | Some p -> Ldot(p, mtn))

let parser classtype_path =
  | mp:{m:extended_module_path STR(".")}? cn:class_name ->
      (match mp with
       | None   -> Lident cn
       | Some p -> Ldot(p, cn))

let parser opt_variance =
  | v:RE("[+-]")? ->
#ifversion >= 4.02
      (match v with
       | None     -> Invariant
       | Some "+" -> Covariant
       | Some "-" -> Contravariant
       | _        -> assert false)
#else
      (match v with
       | None     -> (false, false)
       | Some "+" -> (true , false)
       | Some "-" -> false, true
       | _        -> assert false)
#endif

let parser override_flag =
    o:STR("!")? -> (if o <> None then Override else Fresh)

(****************************************************************************
 * Attributes (parsed but ignored for ocaml < 4.02                     *
 ****************************************************************************)

let parser attr_id =
  | id:ident l:{ '.' id:ident}* ->
      id_loc (String.concat "." (id::l)) _loc

#ifversion < 4.02
type attr =
    PStr of structure_item list
  | PTyp of core_type
  | PPat of pattern * expression option
#endif

let parser payload =
  | s:structure -> PStr(s)
  | CHR(':') t:typexpr -> PTyp(t)
  | CHR('?') p:pattern e:{STR("when") e:expression}? -> PPat(p,e)

let parser attribute =
  | STR("[@") id:attr_id p:payload ']'

let parser attributes =
  | {a:attribute}*

let parser ext_attributes =
  | a:{CHR('%') a:attribute}? l:attributes -> a, l

let parser post_item_attributes =
  | l:{STR("[@@") id:attr_id p:payload CHR(']')}*

let parser ext_attributes =
  | l:{STR("[@@@") id:attr_id p:payload CHR(']')}*

let parser extension =
  | STR("[%") id:attr_id p:payload CHR(']')

let parser item_extension =
  | STR("[%%") id:attr_id p:payload CHR(']')

(****************************************************************************
 * Type expressions                                                         *
 ****************************************************************************)
let parser only_poly_typexpr =
#ifversion >= 4.05
  | ids:{STR("'") id:ident -> id_loc id _loc}+ STR(".") te:typexpr ->
#else
  | ids:{STR("'") id:ident}+ STR(".") te:typexpr ->
#endif
      loc_typ _loc (Ptyp_poly (ids, te))

let parser poly_typexpr =
#ifversion >= 4.05
  | ids:{STR("'") id:ident -> id_loc id _loc}+ STR(".") te:typexpr ->
#else
  | ids:{STR("'") id:ident}+ STR(".") te:typexpr ->
#endif
      loc_typ _loc (Ptyp_poly (ids, te))
  | te:typexpr ->
#ifversion >= 4.02
       te
#else
       loc_typ _loc (Ptyp_poly ([], te))
#endif

let parser poly_syntax_typexpr =
#ifversion >= 4.05
  | type_kw ids:{id:typeconstr_name -> id_loc id _loc_id}+ STR(".") te:typexpr ->
#else
  | type_kw ids:typeconstr_name+ STR(".") te:typexpr ->
#endif
       (ids, te)

let parser method_type =
  | mn:method_name STR(":") pte:poly_typexpr ->
#ifversion >= 4.05
      id_loc mn _loc_mn, [], pte
#else
#ifversion >= 4.02
      mn, [], pte
#else
    { pfield_desc = Pfield (mn, pte); pfield_loc = _loc }
#endif
#endif
let parser tag_spec =
  | tn:tag_name te:{_:of_kw '&'? typexpr}? ->
      let amp,t = match te with
              | None   -> true, []
              | Some (amp,l) -> amp<>None, [l]
      in
#ifversion >= 4.02
      Rtag (tn, [], amp, t)
#else
      Rtag (tn, amp, t)
#endif
  | te:typexpr ->
      Rinherit te

let parser tag_spec_first =
  | tn:tag_name te:{_:of_kw '&'? typexpr}? ->
      let amp,t = match te with
              | None   -> true,[]
              | Some (amp,l) -> amp<>None, [l]
      in
#ifversion >= 4.02
      [Rtag (tn, [], amp, t)]
#else
      [Rtag (tn, amp, t)]
#endif
  | te:typexpr? STR("|") ts:tag_spec ->
      match te with
      | None    -> [ts]
      | Some te -> [Rinherit te; ts]

let parser tag_spec_full =
  | tn:tag_name (amp,tes):{of_kw amp:'&'? te:typexpr
    tes:{STR("&") te:typexpr}* -> (amp<>None,(te::tes))}?[true,[]] ->
#ifversion >= 4.02
      Rtag (tn, [], amp, tes)
#else
      Rtag (tn, amp, tes)
#endif
  | te:typexpr ->
      Rinherit te

let parser polymorphic_variant_type : core_type grammar =
  | STR("[") tsf:tag_spec_first tss:{STR("|") ts:tag_spec}* STR("]") ->
#ifversion >= 4.02
      let flag = Closed in
#else
      let flag = true in
#endif
      loc_typ _loc (Ptyp_variant (tsf @ tss, flag, None))
  | STR("[>") ts:tag_spec? tss:{STR("|") ts:tag_spec}* STR("]") ->
      let tss = match ts with
                | None    -> tss
                | Some ts -> ts :: tss
      in
#ifversion >= 4.02
      let flag = Open in
#else
      let flag = false in
#endif
      loc_typ _loc (Ptyp_variant (tss, flag, None))
  | STR("[<") STR("|")? tfs:tag_spec_full tfss:{STR("|") tsf:tag_spec_full}*
    tns:{STR(">") tns:tag_name+}?[[]] STR("]") ->
#ifversion >= 4.02
      let flag = Closed in
#else
      let flag = true in
#endif
      loc_typ _loc (Ptyp_variant (tfs :: tfss, flag, Some tns))

let parser package_constraint =
  | type_kw tc:typeconstr CHR('=') te:typexpr ->
      let tc = id_loc tc _loc_tc in
      (tc, te)

let parser package_type =
  | mtp:modtype_path cs:{with_kw pc:package_constraint
    pcs:{_:and_kw package_constraint}* -> (pc::pcs)}?[[]] ->
      let mtp = id_loc mtp _loc_mtp in
      Ptyp_package (mtp, cs)

let parser opt_present =
  | STR("[>") l:tag_name+ STR("]") -> l
  | EMPTY -> []

let mkoption loc d =
  let loc = ghost loc in
  loc_typ loc (Ptyp_constr(id_loc (Ldot (Lident "*predef*", "option")) loc,[d]))

let extra_types_grammar lvl =
  (alternatives (List.map (fun g -> g lvl) extra_types))

let _ = set_typexpr_lvl (fun @(allow_par, lvl) ->
  parser
  |[@unshared] e:(extra_types_grammar lvl) -> e

  | "'" id:ident when lvl <= AtomType ->
      loc_typ _loc (Ptyp_var id)
  | joker_kw when lvl <= AtomType ->
      loc_typ _loc Ptyp_any
  | '(' module_kw pt:package_type ')' when lvl <= AtomType ->
      loc_typ _loc pt
  | '(' te:typexpr at:attribute* ')' when lvl <= AtomType && allow_par ->
#if version >= 4.02
     { te with ptyp_attributes = at }
#else
     te
#endif
  | ln:ty_opt_label te:(typexpr_lvl (next_type_prio Arr)) arrow_re te':(typexpr_lvl Arr) when lvl <= Arr ->
#if version >= 4.03
    loc_typ _loc (Ptyp_arrow (ln, te, te'))
#else
    loc_typ _loc (Ptyp_arrow (ln, mkoption _loc_te te, te'))
#endif
  | ln:label_name ':' te:(typexpr_lvl (next_type_prio Arr)) arrow_re te':(typexpr_lvl Arr) when lvl <= Arr ->
      loc_typ _loc (Ptyp_arrow (labelled ln, te, te'))

  | te:(typexpr_lvl (next_type_prio Arr)) arrow_re te':(typexpr_lvl Arr) when lvl <= Arr ->
     loc_typ _loc (Ptyp_arrow (nolabel, te, te'))

  | tc:typeconstr when lvl <= AtomType ->
      loc_typ _loc (Ptyp_constr (id_loc tc _loc_tc, []))

  | '(' te:typexpr tes:{',' te:typexpr}+ ')' tc:typeconstr when lvl <= AppType ->
      let constr = id_loc tc _loc_tc in
      loc_typ _loc (Ptyp_constr (constr, te::tes))

  | t:(typexpr_lvl AppType) tc:typeconstr when lvl <= AppType ->
      let constr = id_loc tc _loc_tc in
      loc_typ _loc (Ptyp_constr (constr, [t]))
  | pvt:polymorphic_variant_type when lvl <= AtomType -> pvt
  | '<' rv:".."? '>' when lvl <= AtomType ->
#ifversion >= 4.02
      let ml = if rv = None then Closed else Open in
      loc_typ _loc (Ptyp_object([], ml))
#else
      let ml = if rv = None then [] else [{ pfield_desc = Pfield_var; pfield_loc = _loc_rv}] in
      loc_typ _loc (Ptyp_object ml)
#endif
  | STR("<") mt:method_type mts:{_:semi_col mt:method_type}*
    rv:{_:semi_col rv:".."?}? '>' when lvl <= AtomType ->
#ifversion >= 4.02
      let ml = if rv = None || rv = Some None then Closed else Open in
      loc_typ _loc (Ptyp_object ((mt :: mts), ml))
#else
      let ml = if rv = None || rv = Some None then [] else [{ pfield_desc = Pfield_var; pfield_loc = _loc_rv}] in
      loc_typ _loc (Ptyp_object (mt :: mts @ ml))
#endif
#ifversion >= 4.02
  | STR("#") cp:class_path when lvl <= AtomType ->
      let cp = id_loc cp _loc_cp in
      loc_typ _loc (Ptyp_class (cp, []))
  | STR("(") te:typexpr tes:{STR(",") te:typexpr}* STR(")")
    STR("#") cp:class_path when lvl <= AtomType ->
      let cp = id_loc cp _loc_cp in
      loc_typ _loc (Ptyp_class (cp, te::tes))
#else
  | STR("#") cp:class_path o:opt_present when lvl <= AtomType ->
      let cp = id_loc cp _loc_cp in
      loc_typ _loc (Ptyp_class (cp, [], o))
  | STR("(") te:typexpr tes:{STR(",") te:typexpr}* STR(")")
    STR("#") cp:class_path  o:opt_present when lvl <= AtomType ->
      let cp = id_loc cp _loc_cp in
      loc_typ _loc (Ptyp_class (cp, te::tes, o))
#endif

  | te:(typexpr_lvl (next_type_prio ProdType))
    tes:{_:{'*' | "×"} te:(typexpr_lvl (next_type_prio ProdType)) -> te}+  when lvl <= ProdType->
     loc_typ _loc (Ptyp_tuple (te::tes))

  | te:(typexpr_lvl As) as_kw STR("'") id:ident when lvl <= As ->
     loc_typ _loc (Ptyp_alias (te, id))

#ifversion >= 4.02
  | te:(typexpr_lvl DashType) STR("#") cp:class_path when lvl <= DashType ->
      let cp = id_loc cp _loc_cp in
      loc_typ _loc (Ptyp_class (cp, [te]))
#else
  | te:(typexpr_lvl DashType)
    STR("#") cp:class_path o:opt_present when lvl <= DashType ->
      let cp = id_loc cp _loc_cp in
      loc_typ _loc (Ptyp_class (cp, [te], o))
#endif
  | '$' - aq:{''[a-z]+'' - ':'}?["type"] e:expression - '$' when lvl <= AtomType ->
     begin
       let open Quote in
       let e_loc = exp_ident _loc "_loc" in
       let generic_antiquote e = function
	 | Quote_ptyp -> e
	 | _ -> failwith "invalid antiquotation" (* FIXME: print location *)
       in
       let f =
	 match aq with
	    | "type" -> generic_antiquote e
	    | "tuple" -> generic_antiquote (quote_apply e_loc _loc (pa_ast "typ_tuple") [quote_location_t e_loc _loc _loc; e])
	    | _ -> give_up ()
       in
       Quote.ptyp_antiquotation _loc f
     end
)

(****************************************************************************
 * Type and exception definitions                                           *
 ****************************************************************************)

(* Type definition *)
let parser type_param =
  | var:opt_variance id:{_:'\'' ident} ->
      (Some (id_loc id _loc_id), var)
  | var:opt_variance CHR('_') ->
      (None, var)

let parser type_params =
  | tp:type_param -> [tp]
  | '(' tp:type_param tps:{',' tp:type_param -> tp}* ')' ->
      tp::tps

let parser type_equation =
  | '=' p:private_flag te:typexpr -> (p,te)

let parser type_constraint =
  | constraint_kw id:{_:'\'' ident} '=' te:typexpr ->
      (loc_typ _loc_id (Ptyp_var id), te, _loc)

let parser constr_name2 =
  | cn:constr_name    -> cn
  | '(' ')' -> "()"

let parser of_constr_decl =
  | te:{_:of_kw { _:'(' te:typexpr _:')' -> (te,true)
                  | te:typexpr_nopar -> (te,false) }}? ->
	       let tes =
		 match te with
		 | None   -> []
		 | Some ({ ptyp_desc = Ptyp_tuple tes }, false) -> tes
		 | Some (t,_) -> [t]
	       in
#ifversion >= 4.03
               let tes =  Pcstr_tuple tes in
#endif
               tes
#ifversion >= 4.03
  | of_kw '{' fds:field_decl_list '}' -> Pcstr_record fds
#endif

let parser bar with_bar =
  | EMPTY when not with_bar
  | '|'

let parser constr_decl with_bar =
  | (bar with_bar) cn:constr_name2
    (tes,te):{ te:of_constr_decl -> (te, None)
             | ':' tes:{te:(typexpr_lvl (next_type_prio ProdType))
                        tes:{_:'*' (typexpr_lvl (next_type_prio ProdType))}*
                        arrow_re -> (te::tes)}?[[]]
                   te:(typexpr_lvl (next_type_prio Arr)) ->
#ifversion >= 4.03
                let tes =  Pcstr_tuple tes in
#endif
                (tes, Some te)
#ifversion >= 4.03
             | ':' '{' fds:field_decl_list '}' arrow_re
                   te:(typexpr_lvl (next_type_prio Arr)) ->
                (Pcstr_record fds, Some te)
#endif
             }
    -> let c = id_loc cn _loc_cn in
       constructor_declaration ~attributes:(attach_attrib ~local:true _loc [])
                               _loc c tes te

let parser all_constr_decl with_bar =
  | cd:(constr_decl with_bar) -> [cd]
(*  | dol:CHR('$') - e:(expression_lvl App) - CHR('$') -> Quote.make_antiquotation e*)

let _ = set_grammar constr_decl_list (
  parser
  | cd:(all_constr_decl false) cds:{cd:(all_constr_decl true) -> cd}* -> List.flatten (cd::cds)
  | EMPTY -> []
  )

(* NOTE: OCaml includes the semi column in the position *)
let parser field_decl_semi =
  | m:mutable_flag fn:field_name STR(":") pte:poly_typexpr semi_col ->
      label_declaration _loc (id_loc fn _loc_fn) m pte

let parser field_decl =
  | m:mutable_flag fn:field_name STR(":") pte:poly_typexpr ->
      label_declaration _loc (id_loc fn _loc_fn) m pte

let parser field_decl_aux =
  | EMPTY -> []
  | fs:field_decl_aux fd:field_decl_semi -> fd::fs
  (*  | dol:CHR('$') - e:(expression_lvl App) - CHR('$') STR(";")? ls:field_decl_list -> Quote.make_antiquotation e*)

let _ = set_grammar field_decl_list (
  parser
    | fs:field_decl_aux -> List.rev fs
    | fs:field_decl_aux fd:field_decl -> List.rev (fd::fs)
  )

let parser type_representation =
  | STR("{") fds:field_decl_list STR("}") -> Ptype_record fds
  | cds:constr_decl_list -> if cds = [] then give_up (); Ptype_variant (cds)

let parser type_information =
  | te:type_equation? ptr:{CHR('=') pri:private_flag tr:type_representation}?
    cstrs:type_constraint* ->
      let pri, tkind =
        match ptr with
        | None   -> (Public, Ptype_abstract)
        | Some c -> c
      in
      (pri, te, tkind, cstrs)

let typedef_gen = (fun attach constr filter ->
  parser
  | tps:type_params?[[]] tcn:constr ti:type_information -> (fun prev_loc ->
      let _loc = match
 	  (prev_loc:Location.t option) with None -> _loc
	| Some l -> merge2 l _loc
      in
      let (pri, te, tkind, cstrs) = ti in
      let pri, te = match te with
	  None -> pri, None
	| Some(Private, te) ->
	   if pri = Private then give_up (); (* ty = private ty' = private A | B is not legal *)
	   Private, Some te
	| Some(_, te) -> pri, Some te
      in
      id_loc tcn _loc_tcn,
      type_declaration ~attributes:(if attach then attach_attrib _loc [] else [])
	_loc (id_loc (filter tcn) _loc_tcn) tps cstrs tkind pri te)
   )

let typedef = typedef_gen true typeconstr_name (fun x -> x)
let typedef_in_constraint = typedef_gen false typeconstr Longident.last


let parser type_definition =
#ifversion >= 4.02.0
  | l:type_kw td:typedef tds:{l:and_kw td:typedef -> snd (td (Some _loc_l))}* ->
                             snd (td (Some _loc_l))::tds
#else
  | l:type_kw td:typedef tds:{l:and_kw td:typedef -> td (Some _loc_l)}* ->
                             td (Some _loc_l)::tds
#endif

let parser exception_declaration =
  | exception_kw cn:constr_name te:of_constr_decl -> (id_loc cn _loc_cn, te, _loc)

(* Exception definition *)
let parser exception_definition =
  | exception_kw cn:constr_name CHR('=') c:constr ->
      (let name = id_loc cn _loc_cn in
      let ex = id_loc c _loc_c in
#ifversion >= 4.02
       (Str.exception_ ~loc:_loc (Te.rebind ~loc:(merge2 _loc_cn _loc_c) name ex))).pstr_desc
#else
      Pstr_exn_rebind (name, ex))
#endif
  | (name,ed,_loc'):exception_declaration ->
#ifversion >= 4.02
      (Str.exception_ ~loc:_loc (Te.decl ~loc:_loc ~args:ed name)).pstr_desc
#else
      Pstr_exception (name, ed)
#endif

(****************************************************************************
 * Classes                                                                  *
 ****************************************************************************)
(* Class types *)
let class_field_spec = declare_grammar "class_field_spec"
let class_body_type = declare_grammar "class_body_type"

let parser virt_mut =
  | v:virtual_flag m:mutable_flag -> (v, m)
  | mutable_kw virtual_kw -> (Virtual, Mutable)

let parser virt_priv =
  | v:virtual_flag p:private_flag -> (v, p)
  | private_kw virtual_kw -> (Virtual, Private)

let _ = set_grammar class_field_spec (
  parser
  | inherit_kw cbt:class_body_type ->
#ifversion >= 4.02
      pctf_loc _loc (Pctf_inherit cbt)
#else
      pctf_loc _loc (Pctf_inher cbt)
#endif
  | val_kw (vir,mut):virt_mut ivn:inst_var_name STR(":") te:typexpr ->
#ifversion >= 4.05
        let ivn = id_loc ivn _loc_ivn in
#endif
        pctf_loc _loc (Pctf_val (ivn, mut, vir, te))
  | method_kw (v,pri):virt_priv mn:method_name STR(":") te:poly_typexpr ->
#ifversion >= 4.05
        let mn = id_loc mn _loc_mn in
#endif
#ifversion >= 4.02
        pctf_loc _loc (Pctf_method (mn, pri, v, te))
#else
      (if v = Concrete then
        pctf_loc _loc (Pctf_meth (mn, pri, te))
      else
        pctf_loc _loc (Pctf_virt (mn, pri, te))
      )
#endif
  | constraint_kw te:typexpr CHR('=') te':typexpr ->
#ifversion >= 4.02
      pctf_loc _loc (Pctf_constraint (te, te'))
#else
      pctf_loc _loc (Pctf_cstr (te, te'))
#endif
  )

let _ = set_grammar class_body_type (
  parser
  | object_kw te:{STR("(") te:typexpr STR(")")}? cfs:class_field_spec*
    end_kw ->
      let self = match te with
                 | None   -> loc_typ _loc_te Ptyp_any
                 | Some t -> t
      in
      let sign =
        { pcsig_self = self
        ; pcsig_fields = cfs
#ifversion <= 4.01
        ; pcsig_loc = merge2 _loc_te _loc_cfs
#endif
        }
      in
      pcty_loc _loc (Pcty_signature sign)
  | tes:{STR("[") te:typexpr tes:{STR(",") te:typexpr}*
    STR("]") -> (te::tes)}?[[]] ctp:classtype_path ->
      let ctp = id_loc ctp _loc_ctp in
      pcty_loc _loc (Pcty_constr (ctp, tes))
  )

let parser class_type =
  | tes:{l:maybe_opt_label? STR(":") te:typexpr -> (l, te)}* cbt:class_body_type ->
      let app acc (lab, te) =
#ifversion >= 4.02
        match lab with
        | None   -> pcty_loc _loc (Pcty_arrow (nolabel, te, acc))
#ifversion >= 4.03
        | Some l -> pcty_loc _loc (Pcty_arrow (l, (match l with Optional _ -> te | _ -> te), acc))
#else
        | Some l -> pcty_loc _loc (Pcty_arrow (l, (if l.[0] = '?' then mkoption _loc_tes te else te), acc))
#endif
#else
        match lab with
        | None   -> pcty_loc _loc (Pcty_fun ("", te, acc))
        | Some l -> pcty_loc _loc (Pcty_fun (l, (if l.[0] = '?' then mkoption _loc_tes te else te), acc))
#endif
      in
      List.fold_left app cbt (List.rev tes)

let parser type_parameters =
  | i1:type_param l:{ STR(",") i2:type_param }* -> i1::l

(* Class specification *)
let parser class_spec =
  | v:virtual_flag params:{STR("[") params:type_parameters STR("]")}?[[]]
    cn:class_name STR(":") ct:class_type ->
      class_type_declaration ~attributes:(attach_attrib _loc []) _loc_params _loc (id_loc cn _loc_cn) params v ct

let parser class_specification =
  | cs:class_spec css:{_:and_kw class_spec}* -> (cs::css)

(* Class type definition *)
let parser classtype_def =
  | v:virtual_flag params:{STR("[") tp:type_parameters STR("]")}?[[]] cn:class_name
    CHR('=') cbt:class_body_type ->
      class_type_declaration ~attributes:(attach_attrib _loc []) _loc_params _loc (id_loc cn _loc_cn) params v cbt

let parser classtype_definition =
  | type_kw cd:classtype_def cds:{_:and_kw classtype_def}* ->
      (cd::cds)

(****************************************************************************
 * Constants and Patterns                                                   *
 ****************************************************************************)
let parser integer_litteral = (s,co):int_litteral ->
#ifversion >= 4.03
  Pconst_integer(s,co)
#else
  match co with
  | None     -> const_int (int_of_string s)
  | Some 'l' -> const_int32 (Int32.of_string s)
  | Some 'L' -> const_int64 (Int64.of_string s)
  | Some 'n' -> const_nativeint (Nativeint.of_string s)
  | Some _   -> Earley.give_up ()
#endif

(* Constants *)
let parser constant =
    f:float_litteral   -> const_float f
  | c:char_litteral    -> const_char c
  | s:string_litteral  -> const_string s
  | s:regexp_litteral  -> const_string s
  | s:new_regexp_litteral -> const_string s
  | i:integer_litteral -> i

(* we do like parser.mly from ocaml: neg_constant for pattern only *)
let parser neg_constant =
    {CHR('-') | STR("-.")} f:float_litteral -> const_float ("-"^f)
  | CHR('-') i:integer_litteral ->
     match i with
#ifversion < 4.03
     | Const_int i   -> const_int (-i)
     | Const_int32 i -> const_int32 (Int32.neg i)
     | Const_int64 i -> const_int64 (Int64.neg i)
     | Const_nativeint i -> const_nativeint (Nativeint.neg i)
#else
     | Pconst_integer(s,o) -> Pconst_integer("-"^s,o)
#endif
     | _ -> assert false
(* Patterns *)

let parser extra_patterns_grammar lvl =
  (alternatives (List.map (fun g -> g lvl) extra_patterns))

let _ = set_pattern_lvl (fun @(as_ok,lvl) -> parser
  | [@unshared] e:(extra_patterns_grammar (as_ok, lvl)) -> e

  | [@unshared] p:(pattern_lvl (as_ok, lvl)) as_kw vn:value_name when as_ok ->
      loc_pat _loc (Ppat_alias(p, id_loc vn _loc_vn))

  | vn:value_name when lvl <= AtomPat ->
      loc_pat _loc (Ppat_var (id_loc vn _loc_vn))
  | joker_kw when lvl <= AtomPat ->
      loc_pat _loc Ppat_any
  | c1:char_litteral STR("..") c2:char_litteral when lvl <= AtomPat ->
      let ic1, ic2 = Char.code c1, Char.code c2 in
      if ic1 > ic2 then assert false; (* FIXME error message invalid range *)
#ifversion >= 4.02
      loc_pat _loc (Ppat_interval (const_char (Char.chr ic1), const_char (Char.chr ic2)))
#else
      let const i = Ppat_constant (const_char (Char.chr i)) in
      let rec range acc a b =
        if a > b then assert false
        else if a = b then a::acc
        else range (a::acc) (a+1) b
      in
      let opts = List.map (fun i -> loc_pat _loc (const i)) (range [] ic1 ic2) in
      List.fold_left (fun acc o -> loc_pat _loc (Ppat_or(o, acc))) (List.hd opts) (List.tl opts)
#endifx
  | c:{c:constant | c:neg_constant} when lvl <= AtomPat ->
      loc_pat _loc (Ppat_constant c)
  | '(' p:pattern  ty:{_:':' typexpr}? ')' when lvl <= AtomPat ->
     let p = match ty with
	 None -> loc_pat _loc p.ppat_desc
       | Some ty ->loc_pat _loc (Ppat_constraint(p, ty))
     in
     p
  | lazy_kw p:(pattern_lvl (false,ConstrPat)) when lvl <= ConstrPat ->
      let ast = Ppat_lazy(p) in
      loc_pat _loc ast
#ifversion >= 4.02
  | exception_kw p:(pattern_lvl (false,ConstrPat)) when lvl <= ConstrPat ->
      let ast = Ppat_exception(p) in
      loc_pat _loc ast
#endif
  | c:constr p:(pattern_lvl (false, ConstrPat)) when lvl <= ConstrPat ->
      let ast = ppat_construct(id_loc c _loc_c, Some p) in
      loc_pat _loc ast
  | c:constr when lvl <= AtomPat ->
      let ast = ppat_construct(id_loc c _loc_c, None) in
      loc_pat _loc ast
  | b:bool_lit when lvl <= AtomPat ->
      let fls = id_loc (Lident b) _loc in
      loc_pat _loc (ppat_construct (fls, None))
  | c:tag_name p:(pattern_lvl (false, ConstrPat)) when lvl <= ConstrPat ->
      loc_pat _loc (Ppat_variant (c, Some p))
  | c:tag_name when lvl <= AtomPat ->
      loc_pat _loc (Ppat_variant (c, None))
  | s:'#' t:typeconstr when lvl <= AtomPat ->
      loc_pat _loc (Ppat_type(id_loc t _loc_t))
  | s:'{' f:field p:{'=' p:pattern}? fps:{semi_col f:field
    p:{CHR('=') p:pattern}? -> (id_loc f _loc_f, p)}*
    clsd:{semi_col joker_kw -> ()}? semi_col? '}' when lvl <= AtomPat ->
      let all = (id_loc f _loc_f, p)::fps in
      let f (lab, pat) =
        match pat with
        | Some p -> (lab, p)
        | None   ->
	   let slab = match lab.txt with
                               | Lident s -> id_loc s lab.loc
                               | _        -> give_up ()
                    in (lab, loc_pat lab.loc (Ppat_var slab))
      in
      let all = List.map f all in
      let cl = match clsd with
               | None   -> Closed
               | Some _ -> Open
      in
      loc_pat _loc (Ppat_record (all, cl))
  | STR("[") p:pattern ps:{semi_col p:pattern -> p}* semi_col? c:STR("]") when lvl <= AtomPat ->
      pat_list _loc _loc_c (p::ps)
  | STR("[") STR("]") when lvl <= AtomPat ->
      let nil = id_loc (Lident "[]") _loc in
      loc_pat _loc (ppat_construct (nil, None))
  | STR("[|") p:pattern ps:{semi_col p:pattern -> p}* semi_col? STR("|]") when lvl <= AtomPat ->
      loc_pat _loc (Ppat_array (p::ps))
  | STR("[|") STR("|]") when lvl <= AtomPat ->
      loc_pat _loc (Ppat_array [])
  | STR("(") STR(")") when lvl <= AtomPat ->
      let unt = id_loc (Lident "()") _loc in
      loc_pat _loc (ppat_construct (unt, None))
  | begin_kw end_kw when lvl <= AtomPat ->
      let unt = id_loc (Lident "()") _loc in
      loc_pat _loc (ppat_construct (unt, None))
  | '(' module_kw mn:module_name pt:{STR(":") pt:package_type}? ')' when lvl <= AtomPat ->
      let unpack = Ppat_unpack mn in
      let pat = match pt with
                | None    -> unpack
                | Some pt -> let pt = loc_typ _loc_pt pt in
                             Ppat_constraint (loc_pat _loc_mn unpack, pt)
      in
      loc_pat _loc pat
  | '$' - c:uident when lvl <= AtomPat ->
     (try let str = Sys.getenv c in
	  parse_string ~filename:("ENV:"^c) pattern ocaml_blank str
      with Not_found -> give_up ())

  | '$' - aq:{''[a-z]+'' - ':'}?["pat"] e:expression - '$' when lvl <= AtomPat ->
     begin
       let open Quote in
       let e_loc = exp_ident _loc "_loc" in
       let locate _loc e =
	 quote_record e_loc _loc [
	   (parsetree "ppat_desc", e) ;
	   (parsetree "ppat_loc", quote_location_t e_loc _loc _loc) ;
#ifversion >= 4.02
           (parsetree "ppat_attributes", quote_attributes e_loc _loc [])
#endif
	 ]
       in
       let generic_antiquote e = function
	 | Quote_ppat -> e
	 | _ -> failwith
                  ("invalid antiquotation type ppat expected at "^
                     string_location _loc)
       in
       let f =
	 match aq with
	    | "pat" -> generic_antiquote e
	    | "bool"  ->
	       let e = quote_const e_loc _loc (parsetree "Ppat_constant")
		 [quote_apply e_loc _loc (pa_ast "const_bool") [e]]
	       in
	       generic_antiquote (locate _loc e)
	    | "int"  ->
	       let e = quote_const e_loc _loc (parsetree "Ppat_constant")
		 [quote_apply e_loc _loc (pa_ast "const_int") [e]]
	       in
	       generic_antiquote (locate _loc e)
	    | "string"  ->
	       let e = quote_const e_loc _loc (parsetree "Ppat_constant")
		 [quote_apply e_loc _loc (pa_ast "const_string") [e]]
	       in
	       generic_antiquote (locate _loc e)
	    | "list"      ->
	       generic_antiquote (quote_apply e_loc _loc (pa_ast "pat_list") [quote_location_t e_loc _loc _loc; quote_location_t e_loc _loc _loc; e])
	    | "tuple"      ->
	       generic_antiquote (quote_apply e_loc _loc (pa_ast "pat_tuple") [quote_location_t e_loc _loc _loc; e])
	    | "array"      ->
	       generic_antiquote (quote_apply e_loc _loc (pa_ast "pat_array") [quote_location_t e_loc _loc _loc; e])
	    | _ -> give_up ()
      in
      Quote.ppat_antiquotation _loc f
    end

  | p:(pattern_lvl (true, AltPat)) '|' p':(pattern_lvl (false, next_pat_prio AltPat)) when lvl <= AltPat ->
      loc_pat _loc (Ppat_or(p, p'))

  | ps:{ (pattern_lvl (true, next_pat_prio TupPat)) _:','}+
      p:(pattern_lvl (false, next_pat_prio TupPat)) when lvl <= TupPat ->
      loc_pat _loc (Ppat_tuple(ps @ [p]))

  | p:(pattern_lvl (true, next_pat_prio ConsPat)) c:"::" p':(pattern_lvl (false, ConsPat)) when lvl <= ConsPat ->
       let cons = id_loc (Lident "::") _loc_c in
       let args = loc_pat (ghost _loc) (Ppat_tuple [p; p']) in
       loc_pat _loc (ppat_construct(cons, Some args)))

(****************************************************************************
 * Expressions                                                              *
 ****************************************************************************)

let let_re = "\\(let\\)\\|\\(val\\)\\b"

type assoc = NoAssoc | Left | Right

let assoc = function
  Prefix | Dot | Dash | Opp -> NoAssoc
| Prod | Sum | Eq -> Left
| _ -> Right

let infix_prio s =
  match s.[0] with
  | '*' -> if String.length s > 1 && s.[1] = '*' then Pow else Prod
  | '/' | '%' -> Prod
  | '+' | '-' -> Sum
  | ':' -> if String.length s > 1 && s.[1] = '=' then Aff else Cons
  | '<' -> if String.length s > 1 && s.[1] = '-' then Aff else Eq
  | '@' | '^' -> Append
  | '&' -> if String.length s = 1 ||
		(String.length s = 2 && s.[1] = '&') then Conj else Eq
  | '|' -> if String.length s = 2 && s.[1] = '|' then Disj else Eq
  | '=' | '>' | '$' | '!' -> Eq
  | 'o' -> Disj
  | 'm' -> Prod
  | 'a' -> Pow
  | 'l' -> (match s.[1] with 's' -> Pow | _ -> Prod)
  | _ -> Printf.printf "%s\n%!" s; assert false

let prefix_prio s =
  if s = "-" || s = "-." || s = "+" || s = "+." then Opp else Prefix

let array_function loc str name =
  let name = if !fast then "unsafe_" ^ name else name in
  loc_expr loc (Pexp_ident (id_loc (Ldot(Lident str, name)) loc ))

let bigarray_function loc str name =
  let name = if !fast then "unsafe_" ^ name else name in
  let lid = Ldot(Ldot(Lident "Bigarray", str), name) in
  loc_expr loc (Pexp_ident (id_loc lid loc))

let untuplify exp =
  match exp.pexp_desc with
  | Pexp_tuple es -> es
  | _             -> [exp]

let bigarray_get _loc arr arg =
  let get = if !fast then "unsafe_get" else "get" in
  match untuplify arg with
  | [c1] ->
      <:expr<Bigarray.Array1.$lid:get$ $arr$ $c1$ >>
  | [c1;c2] ->
      <:expr<Bigarray.Array2.$lid:get$ $arr$ $c1$ $c2$ >>
  | [c1;c2;c3] ->
      <:expr<Bigarray.Array3.$lid:get$ $arr$ $c1$ $c2$ $c3$ >>
  | coords ->
      <:expr<Bigarray.Genarray.$lid:get$ $arr$ $array:coords$ >>

let bigarray_set _loc arr arg newval =
  let set = if !fast then "unsafe_set" else "set" in
  match untuplify arg with
  | [c1] ->
      <:expr<Bigarray.Array1.$lid:set$ $arr$ $c1$ $newval$>>
  | [c1;c2] ->
      <:expr<Bigarray.Array2.$lid:set$ $arr$ $c1$ $c2$ $newval$>>
  | [c1;c2;c3] ->
      <:expr<Bigarray.Array3.$lid:set$ $arr$ $c1$ $c2$ $c3$ $newval$>>
  | coords ->
      <:expr<Bigarray.Genarray.$lid:set$ $arr$ $array:coords$ $newval$ >>

let parser constructor =
  | m:{ m:module_path STR"." }? id:{id:uident -> id | b:bool_lit -> b } ->
      match m with
      | None   -> Lident id
      | Some m -> Ldot(m, id)

let parser argument =
  | '~' id:lident no_colon ->
        (labelled id, loc_expr _loc_id (Pexp_ident(id_loc (Lident id) _loc_id)))
  | id:ty_label e:(expression_lvl (NoMatch, next_exp App)) ->
       (id, e)
  | id:opt_label ->
       (optional id, loc_expr _loc (Pexp_ident(id_loc (Lident id) _loc)))
  | id:ty_opt_label e:(expression_lvl (NoMatch, next_exp App)) ->
       (id, e)
  | e:(expression_lvl (NoMatch, next_exp App)) ->
       (nolabel, e)

let _ = set_parameter (fun allow_new_type ->
  parser
  | pat:(pattern_lvl (false,AtomPat)) -> `Arg (nolabel, None, pat)
  | '~' '(' id:lident t:{ STR":" t:typexpr }? STR")" -> (
      let pat =  loc_pat _loc_id (Ppat_var(id_loc id _loc_id)) in
      let pat = match t with
      | None   -> pat
      | Some t -> loc_pat _loc (Ppat_constraint (pat, t))
      in
      `Arg (labelled id, None, pat))
  | id:ty_label pat:pattern -> `Arg (id, None, pat)
  | '~' id:lident no_colon -> `Arg (labelled id, None, loc_pat _loc_id (Ppat_var(id_loc id _loc_id)))
  | '?' '(' id:lident t:{ ':' t:typexpr -> t }? e:{'=' e:expression -> e}? ')' -> (
      let pat = loc_pat _loc_id (Ppat_var(id_loc id _loc_id)) in
      let pat = match t with
                | None -> pat
                | Some t -> loc_pat (merge2 _loc_id _loc_t) (Ppat_constraint(pat,t))
      in `Arg (optional id, e, pat))
  | id:ty_opt_label STR"(" pat:pattern t:{':' t:typexpr}? e:{'=' e:expression}? ')' -> (
      let pat = match t with
                | None -> pat
                | Some t -> loc_pat (merge2 _loc_pat _loc_t) (Ppat_constraint(pat,t))
      in `Arg (id, e, pat))
  | id:ty_opt_label pat:pattern -> `Arg (id, None, pat)
  | id:opt_label -> `Arg (optional id, None, loc_pat _loc_id (Ppat_var(id_loc id _loc_id)))
  | '(' type_kw name:typeconstr_name ')' when allow_new_type ->
#ifversion >= 4.05
      let name = id_loc name _loc_name in
#endif
      `Type(name)
  )

let apply_params ?(gh=false) params e =
  let f acc = function
    | `Arg (lbl,opt,pat), _loc' ->
       loc_expr (ghost (merge2 _loc' e.pexp_loc)) (pexp_fun (lbl, opt, pat, acc))
    | `Type name, _loc' ->
       loc_expr (ghost (merge2 _loc' e.pexp_loc)) (Pexp_newtype(name,acc))
  in
  let e = List.fold_left f e (List.rev params) in
  if gh then e else de_ghost e

let apply_params_cls _loc params e =
  let f acc = function
    | `Arg (lbl,opt,pat) ->
      loc_pcl _loc (Pcl_fun(lbl, opt, pat, acc))
    | `Type name -> assert false
  in
  List.fold_left f e (List.rev params)

let parser right_member =
  | l:{lb:(parameter true) -> lb, _loc_lb}+ ty:{CHR(':') t:typexpr}? CHR('=') e:expression ->
      let e = match ty with
	None -> e
      | Some ty -> loc_expr (ghost _loc) (pexp_constraint(e, ty))
      in
      apply_params ~gh:true l e

let parser eright_member =
  | ty:{CHR(':') t:typexpr}? CHR('=') e:expression ->
      let e = match ty with
	None -> e
      | Some ty -> loc_expr (ghost _loc) (pexp_constraint(e, ty))
      in
      e

let _ = set_grammar let_binding (
  parser
  | pat:pattern e:eright_member a:post_item_attributes l:{_:and_kw let_binding}?[[]] ->
     ( let loc = merge2 _loc_pat _loc_e in
       value_binding ~attributes:(attach_attrib loc a) loc pat e::l)
  | vn:value_name e:right_member a:post_item_attributes l:{_:and_kw let_binding}?[[]] ->
     ( let loc = merge2 _loc_vn _loc_e in
       let pat = pat_ident _loc_vn vn  in
       value_binding ~attributes:(attach_attrib loc a) loc pat e::l)
  | vn:value_name ':' ty:only_poly_typexpr '=' e:expression a:post_item_attributes l:{_:and_kw let_binding}?[[]] ->
      let pat = loc_pat _loc (Ppat_constraint(
        loc_pat _loc (Ppat_var(id_loc vn _loc_vn)),
        ty))
      in
      let loc = merge2 _loc_vn _loc_e in
      value_binding ~attributes:(attach_attrib loc a) loc pat e::l
  | vn:value_name ':' (ids,ty):poly_syntax_typexpr '=' e:expression a:post_item_attributes l:{_:and_kw let_binding}?[[]] ->
    let (e, ty) = wrap_type_annotation _loc ids ty e in
    let pat = loc_pat _loc (Ppat_constraint(
	loc_pat _loc (Ppat_var(id_loc vn _loc_vn)),
        ty))
    in
    let loc = merge2 _loc_vn _loc_e in
    value_binding ~attributes:(attach_attrib loc a) loc pat e::l
  | dol:CHR('$') - aq:{c:"bindings" ":" -> c}?["bindings"] e:(expression_lvl (NoMatch,App)) - CHR('$') l:{_:and_kw let_binding}?[[]] ->
     begin
       let open Quote in
       let generic_antiquote e = function
	 | Quote_loc -> e
	 | _ -> failwith "invalid antiquotation" (* FIXME: print location *)
       in
       let f =
	 match aq with
	    | "bindings" -> generic_antiquote e
	    | _ -> give_up ()
       in
       make_list_antiquotation _loc Quote_loc f
    end
  )

let parser match_case c =
  | pat:pattern  w:{_:when_kw expression }? arrow_re e:(expression_lvl c) ->
    make_case pat e w

let _ = set_grammar match_cases (
  parser
  | '|'? l:{(match_case (Let, Seq)) '|'}* x:(match_case (Match, Seq)) no_semi -> l @ [x]
  | EMPTY -> []
  | '$' - aq:{c:"cases" ":" -> c}?["cases"] e:expression - '$' ->
     begin
       let open Quote in
       let generic_antiquote e = function
	 | Quote_loc -> e
	 | _ -> failwith "invalid antiquotation" (* FIXME: print location *)
       in
       let f =
	 match aq with
	    | "cases" -> generic_antiquote e
	    | _ -> give_up ()
       in
       make_list_antiquotation _loc Quote_loc f
    end
  )

let parser type_coercion =
  | STR(":") t:typexpr t':{STR(":>") t':typexpr}? -> (Some t, t')
  | STR(":>") t':typexpr -> (None, Some t')

let parser expression_list =
  | l:{ e:(expression_lvl (NoMatch, next_exp Seq)) _:semi_col -> (e, _loc_e)}* e:(expression_lvl (Match, next_exp Seq)) semi_col?
      -> l @ [e,_loc_e]
  | EMPTY -> []

let parser record_item =
  | f:field CHR('=') e:(expression_lvl (NoMatch, next_exp Seq)) -> (id_loc f _loc_f,e)
  | f:lident -> (let id = id_loc (Lident f) _loc_f in id, loc_expr _loc_f (Pexp_ident(id)))

let parser last_record_item =
  | f:field CHR('=') e:(expression_lvl (Match, next_exp Seq)) -> (id_loc f _loc_f,e)
  | f:lident -> (let id = id_loc (Lident f) _loc_f in id, loc_expr _loc_f (Pexp_ident(id)))

let _ = set_grammar record_list (
  parser
  | l:{ record_item _:semi_col }* it:last_record_item semi_col? -> (l@[it])
(*  | dol:CHR('$') - e:(expression_lvl App) - CHR('$') STR(semi_col)? ls:record_list ->
    push_pop_record (start_pos _loc_dol).Lexing.pos_cnum e @ ls*)
  | EMPTY -> [])

(****************************************************************************
 * classes and objects                                                      *
 ****************************************************************************)

let parser obj_item =
  | v:inst_var_name CHR('=') e:(expression_lvl (Match, next_exp Seq)) (* FIXME match always allowed ?*)
     -> (id_loc v _loc_v, e)

(* Class expression *)

let parser class_expr_base =
  | cp:class_path ->
      let cp = id_loc cp _loc_cp in
      loc_pcl _loc (Pcl_constr (cp, []))
  | '[' te:typexpr tes:{',' te:typexpr}* ']' cp:class_path ->
      let cp = id_loc cp _loc_cp in
      loc_pcl _loc (Pcl_constr (cp, te :: tes))
  | STR("(") ce:class_expr STR(")") ->
      loc_pcl _loc ce.pcl_desc
  | STR("(") ce:class_expr STR(":") ct:class_type STR(")") ->
      loc_pcl _loc (Pcl_constraint (ce, ct))
  | fun_kw ps:(parameter false)+ arrow_re ce:class_expr ->
      apply_params_cls _loc ps ce
  | let_kw r:rec_flag lbs:let_binding in_kw ce:class_expr ->
      loc_pcl _loc (Pcl_let (r, lbs, ce))
  | object_kw cb:class_body end_kw ->
      loc_pcl _loc (Pcl_structure cb)

let _ = set_grammar class_expr (
  parser
  | ce:class_expr_base args:{arg:argument+}? ->
      (match args with
       | None   -> ce
       | Some l -> loc_pcl _loc (Pcl_apply (ce, l)))
  )

let parser class_field =
  | inherit_kw o:override_flag ce:class_expr
#ifversion >= 4.05
               id:{_:as_kw id:lident -> id_loc id _loc_id}? ->
#else
               id:{_:as_kw lident}? ->
#endif
#ifversion >= 4.02
      loc_pcf _loc (Pcf_inherit (o, ce, id))
#else
      loc_pcf _loc (Pcf_inher (o, ce, id))
#endif
  | val_kw o:override_flag m:mutable_flag ivn:inst_var_name te:{CHR(':') t:typexpr}?
    CHR('=') e:expression ->
      let ivn = id_loc ivn _loc_ivn in
      let ex =
        match te with
        | None   -> e
        | Some t -> loc_expr (ghost _loc_te) (pexp_constraint (e, t))
      in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_val (ivn, m, Cfk_concrete(o,ex)))
#else
      loc_pcf _loc (Pcf_val (ivn, m, o, ex))
#endif
  | val_kw m:mutable_flag virtual_kw ivn:inst_var_name
    STR(":") te:typexpr ->
      let ivn = id_loc ivn _loc_ivn in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_val (ivn, m, Cfk_virtual te))
#else
      loc_pcf _loc (Pcf_valvirt (ivn, m, te))
#endif
  | val_kw virtual_kw mutable_kw ivn:inst_var_name STR(":") te:typexpr ->
      let ivn = id_loc ivn _loc_ivn in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_val (ivn, Mutable, Cfk_virtual te))
#else
      loc_pcf _loc (Pcf_valvirt (ivn, Mutable, te))
#endif
  | method_kw o:override_flag p:private_flag mn:method_name
    STR(":") te:poly_typexpr CHR('=') e:expression ->
      let mn = id_loc mn _loc_mn in
      let e = loc_expr _loc (Pexp_poly (e, Some te)) in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_method (mn, p, Cfk_concrete(o,e)))
#else
      loc_pcf _loc (Pcf_meth (mn, p, o, e))
#endif
  | method_kw o:override_flag p:private_flag mn:method_name
    STR(":") (ids,te):poly_syntax_typexpr CHR('=') e:expression ->
      let mn = id_loc mn _loc_mn in
      let e, poly =  wrap_type_annotation _loc ids te e in
      let e = loc_expr _loc (Pexp_poly (e, Some poly)) in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_method (mn, p, Cfk_concrete(o,e)))
#else
      loc_pcf _loc (Pcf_meth (mn, p, o, e))
#endif
  | method_kw o:override_flag p:private_flag mn:method_name ps:{p:(parameter true) -> p,_loc_p}*
      te:{STR(":") te:typexpr}? CHR('=') e:expression ->
      if ps = [] && te <> None then give_up ();
      let mn = id_loc mn _loc_mn in
      let e =
	match te with
	  None -> e
	| Some te ->
	   loc_expr (ghost _loc) (pexp_constraint (e, te))
      in
      let e : expression = apply_params ps e in
      let e = loc_expr _loc (Pexp_poly (e, None)) in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_method (mn, p, Cfk_concrete(o,e)))
#else
      loc_pcf _loc (Pcf_meth (mn, p, o, e))
#endif
  | method_kw p:private_flag virtual_kw mn:method_name STR(":") pte:poly_typexpr ->
      let mn = id_loc mn _loc_mn in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_method (mn, p, Cfk_virtual(pte)))
#else
      loc_pcf _loc (Pcf_virt (mn, p, pte))
#endif
  | method_kw virtual_kw private_kw mn:method_name STR(":") pte:poly_typexpr ->
      let mn = id_loc mn _loc_mn in
#ifversion >= 4.02
      loc_pcf _loc (Pcf_method (mn, Private, Cfk_virtual(pte)))
#else
      loc_pcf _loc (Pcf_virt (mn, Private, pte))
#endif
  | constraint_kw te:typexpr CHR('=') te':typexpr ->
#ifversion >= 4.02
      loc_pcf _loc (Pcf_constraint (te, te'))
#else
      loc_pcf _loc (Pcf_constr (te, te'))
#endif
  | initializer_kw e:expression ->
#ifversion >= 4.02
      loc_pcf _loc (Pcf_initializer e)
#else
      loc_pcf _loc (Pcf_init e)
#endif

let _ = set_grammar class_body (
  parser
  | p:pattern? f:class_field* ->
      let p = match p with None -> loc_pat _loc_p Ppat_any | Some p -> p in
#ifversion >= 4.02
      { pcstr_self = p; pcstr_fields = f }
#else
      { pcstr_pat = p; pcstr_fields = f }
#endif
  )

(* Class definition *)
let parser class_binding =
  | v:virtual_flag params:{STR("[") params:type_parameters STR("]")}?[[]]
    cn:class_name ps:(parameter false)* ct:{STR(":") ct:class_type}? CHR('=')
    ce:class_expr ->
      let ce = apply_params_cls _loc ps ce in
      let ce = match ct with
               | None    -> ce
               | Some ct -> loc_pcl _loc (Pcl_constraint(ce, ct))
      in
      class_type_declaration ~attributes:(attach_attrib _loc []) _loc_params _loc (id_loc cn _loc_cn) params v ce

let parser class_definition =
  | cb:class_binding cbs:{_:and_kw class_binding}* -> (cb::cbs)

let pexp_list _loc ?loc_cl l =
  if l = [] then
    loc_expr _loc (pexp_construct(id_loc (Lident "[]") _loc, None))
  else
    let loc_cl = ghost (match loc_cl with None -> _loc | Some pos -> pos) in
    List.fold_right (fun (x,pos) acc ->
		     let _loc = ghost (merge2 pos loc_cl) in
		     loc_expr _loc (pexp_construct(id_loc (Lident "::") (ghost _loc), Some (loc_expr _loc (Pexp_tuple [x;acc])))))
		    l (loc_expr loc_cl (pexp_construct(id_loc (Lident "[]") loc_cl, None)))


let apply_lbl _loc (lbl, e) =
  let e = match e with
      None -> loc_expr _loc (Pexp_ident(id_loc (Lident lbl) _loc ))
    | Some e -> e
  in (lbl, e)

let rec mk_seq = function
      | [] -> assert false
      | [e] -> e
      | x::l ->
	 let res = mk_seq l in
	 loc_expr (merge2 x.pexp_loc res.pexp_loc) (Pexp_sequence(x,res))

(* Expressions *)
let parser extra_expressions_grammar lvl =
  (alternatives (List.map (fun g -> g lvl) extra_expressions))

let structure_item_simple = declare_grammar "structure_item_simple"

let prefix_expression = parser
  | function_kw l:match_cases -> <:expr< function $cases:l$>>

  | match_kw e:expression with_kw l:match_cases -> <:expr< match $e$ with $cases:l$>>

  | try_kw e:expression with_kw l:match_cases -> <:expr< try $e$ with $cases:l$>>

  | e:(alternatives extra_prefix_expressions) -> e

let if_expression (alm,lvl) = parser
  | if_kw c:expression then_kw e:(expression_lvl(Match, next_exp Seq)) else_kw e':(expression_lvl (alm, next_exp Seq)) ->
     <:expr< if $c$ then $e$ else $e'$>>

  | if_kw c:expression then_kw e:(expression_lvl (alm, next_exp Seq)) no_else ->
     <:expr< if $c$ then $e$>>

let _ = set_expression_lvl (fun ((alm,lvl) as c) -> parser

  | e:(extra_expressions_grammar c) -> e

  | e:((expression_lvl (left_alm alm, next_exp lvl))) when lvl < Atom && lvl != Seq -> e

  | ls:{(expression_lvl (NoMatch, next_exp Seq)) _:semi_col }*
      e':(expression_lvl (right_alm alm, next_exp Seq)) {semi_col | no_semi} when lvl = Seq ->
        (* NOTE: why OCaml does that for the final ';' and the pos of e'
           this will disappear if the reported bug is fixed in ocaml *)
        let e' = if Quote.is_antiquotation e'.pexp_loc then e' else
                   loc_expr (merge2 e'.pexp_loc _loc) e'.pexp_desc
        in
	mk_seq (ls@[e'])

  | v:inst_var_name STR("<-") e:(expression_lvl (right_alm alm, next_exp Aff)) when lvl = Aff ->
      loc_expr _loc (Pexp_setinstvar(id_loc v _loc_v, e))

  | id:value_path when lvl = Atom -> loc_expr _loc (Pexp_ident(id_loc id _loc_id))

  | c:constant when lvl = Atom -> loc_expr _loc (Pexp_constant c)

  | mp:module_path STR(".") STR("(") e:expression STR(")") when lvl = Atom ->
      let mp = id_loc mp _loc_mp in
      loc_expr _loc (Pexp_open (Fresh, mp, e))
  | mp:module_path '.' '[' l:expression_list cl: ']' when lvl = Atom ->
      let mp = id_loc mp _loc_mp in
      loc_expr _loc (Pexp_open (Fresh, mp, loc_expr _loc (pexp_list _loc ~loc_cl:_loc_cl l).pexp_desc))
  | mp:module_path '.' '{' e:{expression _:with_kw}? l:record_list '}' when lvl = Atom ->
      let mp = id_loc mp _loc_mp in
      loc_expr _loc (Pexp_open (Fresh, mp, loc_expr _loc (Pexp_record(l,e))))

  | e:prefix_expression when allow_match alm && lvl < App && lvl != Seq -> e

  | e:(if_expression c) when (allow_let alm && lvl < App && lvl != Seq) || lvl = If -> e

  | fun_kw l:{lbl:(parameter true) -> lbl,_loc_lbl}* arrow_re e:(expression_lvl(alm,Seq)) no_semi when allow_let alm && lvl < App && lvl != Seq ->
     loc_expr _loc (apply_params l e).pexp_desc

  | let_kw r:{r:rec_flag l:let_binding in_kw e:(expression_lvl (right_alm alm,Seq)) no_semi
                  -> (fun _loc -> loc_expr _loc (Pexp_let (r, l, e)))
#ifversion >= 4.02
             | module_kw mn:module_name l:{ '(' mn:module_name mt:{':' mt:module_type}? ')' -> (mn, mt, _loc)}*
#else
             | module_kw mn:module_name l:{ '(' mn:module_name ':' mt:module_type ')' -> (mn, mt, _loc)}*
#endif
                 mt:{STR":" mt:module_type }? STR"=" me:module_expr in_kw e:(expression_lvl (right_alm alm,Seq))  ->
               (let me = match mt with None -> me | Some mt -> mexpr_loc (merge2 _loc_mt _loc_me) (Pmod_constraint(me, mt)) in
               let me = List.fold_left (fun acc (mn,mt,_loc) ->
                 mexpr_loc (merge2 _loc _loc_me) (Pmod_functor(mn, mt, acc))) me (List.rev l) in
               fun _loc -> loc_expr _loc (Pexp_letmodule(mn, me, e)))
             | open_kw o:override_flag mp:module_path in_kw
		 e:(expression_lvl (right_alm alm,Seq)) ->
	      (let mp = id_loc mp _loc_mp in
		fun _loc -> loc_expr _loc (Pexp_open (o, mp, e)))
             } when allow_let alm && lvl < App && lvl <> Seq -> r _loc

  | '(' e:expression? ')' when lvl = Atom ->
       (match e with
        | Some(e) -> if Quote.is_antiquotation e.pexp_loc then e
                     else loc_expr _loc e.pexp_desc
        | None ->
	   let cunit = id_loc (Lident "()") _loc in
	   loc_expr _loc (pexp_construct(cunit, None)))

  | '(' no_parser e:expression t:type_coercion ')'  when lvl = Atom  ->
       (match t with
	   | (Some t1, None) -> loc_expr (ghost _loc) (pexp_constraint(e, t1))
	   | (t1, Some t2) -> loc_expr (ghost _loc) (pexp_coerce(e, t1, t2))
	   | None, None -> assert false)

  | begin_kw e:expression? end_kw when lvl = Atom ->
       (match e with
        | Some e ->
           if Quote.is_antiquotation e.pexp_loc then e
           else loc_expr _loc e.pexp_desc
        | None ->
           let cunit = id_loc (Lident "()") _loc in
           loc_expr _loc (pexp_construct(cunit, None)))

  | assert_kw e:{ false_kw -> pexp_assertfalse _loc
                | _:no_false e:(expression_lvl (NoMatch, next_exp App)) when lvl = App ->
                                             Pexp_assert(e) } when (lvl = App) ->
       (loc_expr _loc e)

  | lazy_kw e:(expression_lvl (NoMatch, next_exp App)) when lvl = App ->
     loc_expr _loc (Pexp_lazy e)

  | c:constructor no_dot when lvl = Atom ->
	loc_expr _loc (pexp_construct(id_loc c _loc_c, None))

  | l:tag_name  when lvl = Atom ->
     loc_expr _loc (Pexp_variant(l, None))

  | "[|" l:expression_list "|]" when lvl = Atom ->
     loc_expr _loc (Pexp_array (List.map fst l))

  | '[' l:expression_list cl:']' when lvl = Atom ->
     loc_expr _loc (pexp_list _loc ~loc_cl:_loc_cl l).pexp_desc

  | STR("{") e:{expression _:with_kw}? l:record_list STR("}") when lvl = Atom ->
      loc_expr _loc (Pexp_record(l,e))

  | while_kw e:expression do_kw e':expression done_kw when lvl = Atom ->
      loc_expr _loc (Pexp_while(e, e'))

#ifversion >= 4.02
  | for_kw id:pattern CHR('=') e:expression d:downto_flag e':expression do_kw e'':expression done_kw when lvl = Atom ->
      loc_expr _loc (Pexp_for(id, e, e', d, e''))
#else
  | for_kw id:lident CHR('=') e:expression d:downto_flag e':expression do_kw e'':expression done_kw when lvl = Atom ->
      loc_expr _loc (Pexp_for(id_loc id _loc_id, e, e', d, e''))
#endif

  | new_kw p:class_path when lvl = Atom -> loc_expr _loc (Pexp_new(id_loc p _loc_p))

  | object_kw o:class_body end_kw when lvl = Atom -> loc_expr _loc (Pexp_object o)

  | "{<" l:{ o:obj_item l:{_:semi_col o:obj_item}* _:semi_col? -> o::l }?[[]] ">}" when lvl = Atom ->
     loc_expr _loc (Pexp_override l)

  | '(' module_kw me:module_expr pt:{STR(":") pt:package_type}? ')' when lvl = Atom ->
      let desc = match pt with
                 | None    -> Pexp_pack me
                 | Some pt -> let me = loc_expr (ghost _loc) (Pexp_pack me) in
                              let pt = loc_typ (ghost _loc) pt in
                              pexp_constraint (me, pt)
      in loc_expr _loc desc

| "<:" r:{ "expr"      '<' e:expression            ">>" -> let e_loc = exp_ident _loc "_loc" in Quote.quote_expression e_loc _loc_e e
	 | "type"      '<' e:typexpr               ">>" -> let e_loc = exp_ident _loc "_loc" in Quote.quote_core_type  e_loc _loc_e e
	 | "pat"       '<' e:pattern               ">>" -> let e_loc = exp_ident _loc "_loc" in Quote.quote_pattern    e_loc _loc_e e
	 | "struct"    '<' e:structure_item_simple ">>" -> let e_loc = exp_ident _loc "_loc" in Quote.quote_structure  e_loc _loc_e e
	 | "sig"       '<' e:signature_item        ">>" -> let e_loc = exp_ident _loc "_loc" in Quote.quote_signature  e_loc _loc_e e
	 | "constructors"
	     '<' e:constr_decl_list ">>" ->
#ifversion < 4.02
	   let quote_constructor_declaration e_loc _loc (s,t,t',l) =
	     Quote.(quote_tuple e_loc _loc [
	       ((quote_loc quote_string) e_loc _loc s) ;
	       ((quote_list quote_core_type) e_loc _loc t) ;
	       ((quote_option quote_core_type) e_loc _loc t') ;
	       (quote_location_t e_loc _loc l) ; ])
           in
#endif
	   let e_loc = exp_ident _loc "_loc" in
           Quote.(quote_list quote_constructor_declaration e_loc _loc_e e)
	 | "fields"    '<' e:field_decl_list ">>" ->
#ifversion < 4.02
	   let quote_label_declaration e_loc _loc (x1,x2,x3,x4) =
	     Quote.(quote_tuple e_loc _loc [quote_loc quote_string e_loc _loc x1;
					    quote_mutable_flag e_loc _loc x2;
			       quote_core_type e_loc _loc x3;quote_location_t e_loc _loc x4;])
	   in
#endif
	   let e_loc = exp_ident _loc "_loc" in
	   Quote.(quote_list quote_label_declaration e_loc _loc_e e)
	 | "bindings"  '<' e:let_binding     ">>" ->
#ifversion < 4.02
	   let quote_value_binding e_loc _loc (x1,x2) =
	     Quote.(quote_tuple e_loc _loc [quote_pattern e_loc _loc x1;quote_expression e_loc _loc x2;])
	   in
#endif
	   let e_loc = exp_ident _loc "_loc" in
	   Quote.(quote_list quote_value_binding e_loc _loc_e e)
	 | "cases"     '<' e:match_cases ">>" ->
#ifversion < 4.02
	   let quote_case e_loc _loc (x1,x2) =
	     Quote.(quote_tuple e_loc _loc [quote_pattern e_loc _loc x1;quote_expression e_loc _loc x2;])
	   in
#endif
	   let e_loc = exp_ident _loc "_loc" in
	   Quote.(quote_list quote_case e_loc _loc_e e)
	 | "module"    '<' e:module_expr ">>" ->
	    let e_loc = exp_ident _loc "_loc" in
	    Quote.quote_module_expr e_loc _loc_e e
	 | "module" "type" '<' e:module_type ">>" ->
	    let e_loc = exp_ident _loc "_loc" in
	    Quote.quote_module_type e_loc _loc_e e
	 | "record"    '<' e:record_list     ">>" ->
	    let e_loc = exp_ident _loc "_loc" in
	    let quote_fields = Quote.(quote_list
	      (fun e_loc _loc (x1,x2) -> quote_tuple e_loc _loc [(quote_loc quote_longident) e_loc _loc x1;
						     quote_expression e_loc _loc x2;]))
	    in
	    quote_fields e_loc _loc_e e
	 } when lvl = Atom
	-> r

  | '$' - c:uident when lvl = Atom ->
     (match c with
     | "FILE" ->
	 exp_string _loc ((start_pos _loc).Lexing.pos_fname)
      | "LINE" ->
	 exp_int _loc ((start_pos _loc).Lexing.pos_lnum)
      | _ ->
	 try let str = Sys.getenv c in
	     parse_string ~filename:("ENV:"^c) expression ocaml_blank str
	 with Not_found -> give_up ())

  | '$' - aq:{''[a-z]+'' - ':'}?["expr"] e:expression - '$' when lvl = Atom ->
    let f =
      let open Quote in
      let e_loc = exp_ident _loc "_loc" in
      let locate _loc e =
	quote_record e_loc _loc
              [ (parsetree "pexp_desc", e)
              ; (parsetree "pexp_loc", quote_location_t e_loc _loc _loc)
#ifversion >= 4.02
              ; (parsetree "pexp_attributes", quote_attributes e_loc _loc [])
#endif
	      ]
      in
      let generic_antiquote e =
        function
        | Quote_pexp -> e
         | _          ->
            failwith "Bad antiquotation..." (* FIXME:add location *)
      in
      let quote_loc _loc e =
        quote_record e_loc _loc
          [ ((Ldot(Lident "Asttypes", "txt")), e)
          ; ((Ldot(Lident "Asttypes", "loc")), quote_location_t e_loc _loc _loc) ]
      in
      match aq with
      | "expr"      -> generic_antiquote e
      | "longident" ->
          let e = quote_const e_loc _loc (parsetree "Pexp_ident") [quote_loc _loc e] in
          generic_antiquote (locate _loc e)
      | "bool"      ->
	 generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_bool") [quote_location_t e_loc _loc _loc; e])
      | "int"       ->
	 generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_int") [quote_location_t e_loc _loc _loc; e])
      | "float"     ->
	 generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_float") [quote_location_t e_loc _loc _loc; e])
      | "string"    ->
	 generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_string") [quote_location_t e_loc _loc _loc; e])
      | "char"      ->
	 generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_char") [quote_location_t e_loc _loc _loc; e])
      | "list"      ->
	 generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_list") [quote_location_t e_loc _loc _loc; e])
      | "tuple"      ->
	 generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_tuple") [quote_location_t e_loc _loc _loc; e])
      | "array"      ->
	generic_antiquote (quote_apply e_loc _loc (pa_ast "exp_array") [quote_location_t e_loc _loc _loc; e])
      | _      -> give_up ()
    in
    Quote.pexp_antiquotation _loc f

  | l:{(expression_lvl (NoMatch, next_exp Tupl)) _:',' }+ e':(expression_lvl (right_alm alm, next_exp Tupl))
      when lvl = Tupl ->
       loc_expr _loc (Pexp_tuple (l@[e']))

  | e':{e':(expression_lvl (NoMatch, Dot)) -> e'} '.'
      r:{ STR("(") f:expression STR(")") STR("<-") e:(expression_lvl (right_alm alm,next_exp Aff)) when lvl = Aff ->
	   fun e' _loc -> exp_apply _loc (array_function (ghost (merge2 e'.pexp_loc _loc)) "Array" "set") [e';f;e]

        | STR("(") f:expression STR(")") when lvl = Dot ->
	   fun e' _loc -> exp_apply _loc (array_function (ghost (merge2 e'.pexp_loc _loc)) "Array" "get") [e';f]

	| STR("[") f:expression STR("]") STR("<-") e:(expression_lvl (right_alm alm, next_exp Aff)) when lvl = Aff ->
	   fun e' _loc -> exp_apply _loc (array_function (ghost (merge2 e'.pexp_loc _loc)) "String" "set") [e';f;e]

	| STR("[") f:expression STR("]")  when lvl = Dot ->
	   fun e' _loc -> exp_apply _loc (array_function (ghost (merge2 e'.pexp_loc _loc)) "String" "get") [e';f]

	| STR("{") f:expression STR("}") STR("<-") e:(expression_lvl (right_alm alm, next_exp Aff)) when lvl = Aff ->
	   fun e' _loc -> bigarray_set (ghost (merge2 e'.pexp_loc _loc)) e' f e

	| STR("{") f:expression STR("}") when lvl = Dot ->
	   fun e' _loc -> bigarray_get (ghost (merge2 e'.pexp_loc _loc)) e' f

	| f:field STR("<-") e:(expression_lvl (right_alm alm, next_exp Aff)) when lvl = Aff ->
	   fun e' _loc ->
            let f = id_loc f _loc_f in loc_expr _loc (Pexp_setfield(e',f,e))

	| f:field when lvl = Dot ->
	   fun e' _loc ->
	     let f = id_loc f _loc_f in loc_expr _loc (Pexp_field(e',f)) } when lvl = Dot || lvl = Aff -> r e' _loc

  | e':(expression_lvl (NoMatch, Dash)) '#' f:method_name when lvl = Dash ->
#ifversion >= 4.05
       let f = id_loc f _loc_f in
#endif
       loc_expr _loc (Pexp_send(e',f))

  | f:(expression_lvl (NoMatch, next_exp App)) l:argument+ when lvl = App ->
     loc_expr _loc (match f.pexp_desc, l with
#ifversion >= 4.03
     | Pexp_construct(c,None), [Nolabel, a] ->  Pexp_construct(c,Some a)
#else
#ifversion >= 4.02
     | Pexp_construct(c,None), ["", a] ->  Pexp_construct(c,Some a)
#else
     | Pexp_construct(c,None,b), ["", a] ->  Pexp_construct(c,Some a,b)
#endif
#endif
#ifversion >= 4.03
     | Pexp_variant(c,None), [Nolabel, a] -> Pexp_variant(c,Some a)
#else
     | Pexp_variant(c,None), ["", a] -> Pexp_variant(c,Some a)
#endif
     | _ -> Pexp_apply(f,l))

  | (alternatives
       (List.map (fun lvl0 -> parser p:(prefix_symbol lvl0) e:(expression_lvl (right_alm alm,lvl0))
	 when lvl = lvl0 -> mk_unary_opp p _loc_p e _loc_e) prefix_prios))

  | (alternatives
       (List.map (fun lvl0 ->
	 parser
	   let left, right = if assoc lvl0 = Left then lvl0, next_exp lvl0 else next_exp lvl0, lvl0 in
	   e':(expression_lvl (NoMatch,left))
	   op:(infix_symbol lvl0) e:(expression_lvl (right_alm alm,right)) when lvl = lvl0 ->
       (loc_expr _loc
          (if op = "::" then
            pexp_construct(id_loc (Lident "::") _loc_op, Some (loc_expr (ghost _loc) (Pexp_tuple [e';e])))
          else
            Pexp_apply(loc_expr _loc_op (Pexp_ident(id_loc (Lident op) _loc_op)),
                       [(nolabel, e') ; (nolabel, e)])))) infix_prios)))


(****************************************************************************
 * Module expressions (module implementations)                              *
 ****************************************************************************)

let parser module_expr_base =
  | mp:module_path ->
      let mid = id_loc mp _loc in
      mexpr_loc _loc (Pmod_ident mid)
  | struct_kw ms:structure end_kw ->
      mexpr_loc _loc (Pmod_structure(ms))
#ifversion >= 4.02
  | functor_kw '(' mn:module_name mt:{':' mt:module_type}? ')'
#else
  | functor_kw '(' mn:module_name ':' mt:module_type ')'
#endif
    arrow_re me:module_expr -> mexpr_loc _loc (Pmod_functor(mn, mt, me))
  | '(' me:module_expr mt:{':' mt:module_type}? ')' ->
      (match mt with
       | None    -> me
       | Some mt -> mexpr_loc _loc (Pmod_constraint (me, mt)))
  | '(' val_kw e:expression pt:{STR(":") pt:package_type}? ')' ->
      let e = match pt with
              | None    -> Pmod_unpack e
              | Some pt -> let pt = loc_typ _loc_pt pt in
                           Pmod_unpack (loc_expr (ghost _loc) (pexp_constraint (e, pt)))
      in
      mexpr_loc _loc e
(*  | dol:CHR('$') - e:(expression_lvl App) - CHR('$') -> push_pop_module_expr (start_pos _loc_dol).Lexing.pos_cnum e*)

let _ = set_grammar module_expr (
  parser
    m:module_expr_base l:{STR("(") m:module_expr STR(")") -> (_loc, m)}* ->
      List.fold_left (fun acc (_loc_n, n) -> mexpr_loc (merge2 _loc_m _loc_n) (Pmod_apply(acc, n))) m l
  )

let parser module_type_base =
  | mp:modtype_path ->
      let mid = id_loc mp _loc in
      mtyp_loc _loc (Pmty_ident mid)
  | sig_kw ms:signature end_kw ->
     mtyp_loc _loc (Pmty_signature(ms))
#ifversion >= 4.02
  | functor_kw '(' mn:module_name mt:{':' mt:module_type}? ')'
#else
  | functor_kw '(' mn:module_name ':' mt:module_type ')'
#endif
     arrow_re me:module_type no_with -> mtyp_loc _loc (Pmty_functor(mn, mt, me))
  | STR("(") mt:module_type STR(")") -> mt
  | module_kw type_kw of_kw me:module_expr -> mtyp_loc _loc (Pmty_typeof me)
(*  | dol:CHR('$') - e:(expression_lvl App) - CHR('$') -> push_pop_module_type (start_pos _loc_dol).Lexing.pos_cnum e*)

let parser mod_constraint =
  | t:type_kw tf:typedef_in_constraint -> let (tn,ty) = tf (Some _loc_t) in
#ifversion >= 4.02
     Pwith_type(tn,ty)
#else
     (tn, Pwith_type(ty))
#endif
  | module_kw m1:module_path CHR('=') m2:extended_module_path ->
     let name = id_loc m1 _loc_m1 in
#ifversion >= 4.02
     Pwith_module(name, id_loc m2 _loc_m2 )
#else
     (name, Pwith_module(id_loc m2 _loc_m2 ))
#endif
  | type_kw tps:type_params?[[]] tcn:typeconstr_name STR(":=") te:typexpr ->
      let td = type_declaration _loc (id_loc tcn _loc_tcn)
	   tps [] Ptype_abstract Public (Some te) in
#ifversion >= 4.02
      Pwith_typesubst td
#else
      (id_loc (Lident tcn) _loc_tcn, Pwith_typesubst td)
#endif
  | module_kw mn:module_name STR(":=") emp:extended_module_path ->
#ifversion >= 4.02
     Pwith_modsubst(mn, id_loc emp _loc_emp)
#else
     ({ txt = Lident mn.txt; loc = mn.loc}, Pwith_modsubst(id_loc emp _loc_emp))
#endif

let _ = set_grammar module_type (
  parser
    m:module_type_base l:{_:with_kw m:mod_constraint l:{_:and_kw mod_constraint}* -> m::l } ? ->
      (match l with
         None -> m
       | Some l -> mtyp_loc _loc (Pmty_with(m, l)))
  )

let parser structure_item_base =
  | RE(let_re) r:rec_flag l:let_binding ->
     loc_str _loc (match l with
#ifversion < 4.03
#ifversion >= 4.02
       | [{pvb_pat = {ppat_desc = Ppat_any}; pvb_expr = e}] -> pstr_eval e
#else
       | [({ppat_desc = Ppat_any; ppat_loc = _}, e)] -> pstr_eval e
#endif
#endif
       | _                                           -> Pstr_value (r, l))
  | external_kw n:value_name STR":" ty:typexpr STR"=" ls:string_litteral*  a:post_item_attributes ->
      let l = List.length ls in
      if l < 1 || l > 3 then give_up ();
#ifversion >= 4.02
     loc_str _loc (Pstr_primitive({ pval_name = id_loc n _loc_n; pval_type = ty; pval_prim = ls; pval_loc = _loc;
		      pval_attributes = attach_attrib _loc a }))
#else
      loc_str _loc (Pstr_primitive(id_loc n _loc_n, { pval_type = ty; pval_prim = ls;
					pval_loc = _loc
				      }))
#endif
#ifversion >= 4.03
  | td:type_definition -> loc_str _loc (Pstr_type (Recursive, td)) (* FIXME ? *)
#else
  | td:type_definition -> loc_str _loc (Pstr_type td)
#endif
  | ex:exception_definition -> loc_str _loc ex
#ifversion >= 4.02
  | module_kw r:{rec_kw mn:module_name mt:{STR(":") mt:module_type}? CHR('=')
    me:module_expr ms:{and_kw mn:module_name mt:{STR(":") mt:module_type}? CHR('=')
#else
  | module_kw r:{rec_kw mn:module_name STR(":") mt:module_type CHR('=')
    me:module_expr ms:{and_kw mn:module_name STR(":") mt:module_type CHR('=')
#endif
    me:module_expr -> (module_binding _loc mn mt me)}* ->
      let m = (module_binding _loc mn mt me) in
      Pstr_recmodule (m::ms)
#ifversion >= 4.02
  |            mn:module_name l:{ STR"(" mn:module_name mt:{STR":" mt:module_type }? STR")" -> (mn, mt, _loc)}*
#else
  |            mn:module_name l:{ STR"(" mn:module_name STR":" mt:module_type STR ")" -> (mn, mt, _loc)}*
#endif
     mt:{STR":" mt:module_type }? STR"=" me:module_expr ->
    let me = match mt with None -> me | Some mt -> mexpr_loc (merge2 _loc_mt _loc_me) (Pmod_constraint(me,mt)) in
     let me = List.fold_left (fun acc (mn,mt,_loc) ->
       mexpr_loc (merge2 _loc _loc_me) (Pmod_functor(mn, mt, acc))) me (List.rev l) in
#ifversion >= 4.02
     Pstr_module(module_binding _loc mn None me)
#else
     let (name, _, me) = module_binding _loc mn None me in
     Pstr_module(name,me)
#endif
#ifversion >= 4.02
  |            type_kw mn:modtype_name mt:{STR"=" mt:module_type}? a:post_item_attributes ->
      Pstr_modtype{pmtd_name = id_loc mn _loc_mn; pmtd_type = mt;
 		   pmtd_attributes = attach_attrib _loc a; pmtd_loc = _loc }
#else
  |            type_kw mn:modtype_name STR"=" mt:module_type ->
      Pstr_modtype(id_loc mn _loc_mn, mt)
#endif
               } -> loc_str _loc r
  | open_kw o:override_flag m:module_path a:post_item_attributes ->
#ifversion >= 4.02
      loc_str _loc (Pstr_open{ popen_lid = id_loc m _loc_m; popen_override = o; popen_loc = _loc;
 		 popen_attributes = attach_attrib _loc a})
#else
    loc_str _loc (Pstr_open(o, id_loc m _loc_m))
#endif
  | include_kw me:module_expr a:post_item_attributes ->
#ifversion >= 4.02
    loc_str _loc (Pstr_include {pincl_mod = me; pincl_loc = _loc; pincl_attributes = attach_attrib _loc a })
#else
    loc_str _loc (Pstr_include me)
#endif
  | class_kw r:{ ctd:classtype_definition -> Pstr_class_type ctd
               | cds:class_definition -> Pstr_class cds } -> loc_str _loc r
  | "$struct:" e:expression - '$' ->
     let open Quote in
     pstr_antiquotation _loc (function
     | Quote_pstr ->
	let e_loc = exp_ident _loc "_loc" in
#ifversion >= 4.02
	(quote_apply e_loc _loc (pa_ast "loc_str")
	   [quote_location_t e_loc _loc _loc;
	    quote_const e_loc _loc (parsetree "Pstr_include")
	      [quote_record e_loc _loc [
		(parsetree "pincl_loc", quote_location_t e_loc _loc _loc);
		(parsetree "pincl_attributes", quote_list (quote_attribute) e_loc _loc []);
		(parsetree "pincl_mod",
		 quote_apply e_loc _loc (pa_ast "mexpr_loc")
		     [quote_location_t e_loc _loc _loc;
		      quote_const e_loc _loc (parsetree "Pmod_structure")
			[e]])]]])
#else
	(quote_apply e_loc _loc (pa_ast "loc_str")
	   [quote_location_t e_loc _loc _loc;
	    quote_const e_loc _loc (parsetree "Pstr_include")
	      [quote_apply e_loc _loc (pa_ast "mexpr_loc")
		  [quote_location_t e_loc _loc _loc;
		   quote_const e_loc _loc (parsetree "Pmod_structure")
		     [e]]]])
#endif
     | _ -> failwith "Bad antiquotation..." (* FIXME:add location *))

(* FIXME ext_attributes *)
let parser structure_item_aux =
  | _:ext_attributes -> []
  | _:ext_attributes e:expression -> attach_str _loc @ [loc_str _loc_e (pstr_eval e)]
  | s1:structure_item_aux double_semi_col?[()] _:ext_attributes e:(alternatives extra_structure) ->
     List.rev_append e (List.rev_append (attach_str _loc_e) s1)
  | s1:structure_item_aux double_semi_col?[()] _:ext_attributes s2:structure_item_base -> s2 :: (List.rev_append (attach_str _loc_s2) s1)
  | s1:structure_item_aux double_semi_col _:ext_attributes e:expression -> loc_str _loc_e (pstr_eval e) :: (List.rev_append (attach_str _loc_e) s1)

let _ = set_grammar structure_item
  (parser l:structure_item_aux double_semi_col?[()] -> List.rev l)
let _ = set_grammar structure_item_simple
  (parser ls:{l:structure_item_base -> l}* -> ls)

let parser signature_item_base =
  | val_kw n:value_name STR(":") ty:typexpr a:post_item_attributes ->
     loc_sig _loc (psig_value ~attributes:(attach_attrib _loc a) _loc (id_loc n _loc_n) ty [])
  | external_kw n:value_name STR":" ty:typexpr STR"=" ls:string_litteral* a:post_item_attributes ->
      let l = List.length ls in
      if l < 1 || l > 3 then give_up ();
      loc_sig _loc (psig_value ~attributes:(attach_attrib _loc a) _loc (id_loc n _loc_n) ty ls)
  | td:type_definition ->
#ifversion >= 4.03
       loc_sig _loc (Psig_type (Recursive, td))
#else
       loc_sig _loc (Psig_type td)
#endif
  | (name,ed,_loc'):exception_declaration a:post_item_attributes ->
#ifversion >= 4.02
       loc_sig _loc (Psig_exception (Te.decl ~attrs:(attach_attrib _loc' a) ~loc:_loc' ~args:ed name))
#else
       loc_sig _loc (Psig_exception (name, ed))
#endif
  | {module_kw -> attach_sig _loc} rec_kw mn:module_name STR(":") mt:module_type a:post_item_attributes
      ms:{and_kw mn:module_name STR(":") mt:module_type a:post_item_attributes ->
	    (module_declaration ~attributes:(attach_attrib _loc a) _loc mn mt)}* ->
      let loc_first = merge2 _loc_mn _loc_a in
      let m = (module_declaration ~attributes:(attach_attrib loc_first a) loc_first mn mt) in
      loc_sig _loc (Psig_recmodule (m::ms))
#ifversion >= 4.02
  | {module_kw -> attach_sig _loc} r:{mn:module_name l:{ STR"(" mn:module_name mt:{STR":" mt:module_type}? STR ")" -> (mn, mt, _loc)}*
#else
  | module_kw r:{mn:module_name l:{ STR"(" mn:module_name STR":" mt:module_type STR ")" -> (mn, mt, _loc)}*
#endif
                                    STR":" mt:module_type a:post_item_attributes ->
     let mt = List.fold_left (fun acc (mn,mt,_loc) ->
                                  mtyp_loc (merge2 _loc _loc_mt) (Pmty_functor(mn, mt, acc))) mt (List.rev l) in
#ifversion >= 4.02
     Psig_module(module_declaration ~attributes:(attach_attrib _loc a) _loc mn mt)
#else
     let a, b = module_declaration _loc mn mt in
     Psig_module(a,b)
#endif
  |           type_kw mn:modtype_name mt:{ STR"=" mt:module_type }?  a:post_item_attributes ->
#ifversion >= 4.02
  Psig_modtype{pmtd_name = id_loc mn _loc_mn; pmtd_type = mt;
	       pmtd_attributes = attach_attrib _loc a;
	       pmtd_loc = _loc}
#else
     let mt = match mt with
              | None    -> Pmodtype_abstract
              | Some mt -> Pmodtype_manifest mt
     in
     Psig_modtype(id_loc mn _loc_mn, mt)
#endif
		} -> loc_sig _loc r
  | open_kw o:override_flag m:module_path a:post_item_attributes ->
#ifversion >= 4.02
      loc_sig _loc (Psig_open{ popen_lid = id_loc m _loc_m; popen_override = o; popen_loc = _loc;
  		 popen_attributes = attach_attrib _loc a})
#else
    loc_sig _loc (Psig_open(o, id_loc m _loc_m))
#endif
  | include_kw me:module_type a:post_item_attributes ->
#ifversion >= 4.02
    loc_sig _loc (Psig_include {pincl_mod = me; pincl_loc = _loc; pincl_attributes = attach_attrib _loc a })
#else
    loc_sig _loc (Psig_include me)
#endif
  | class_kw r:{ ctd:classtype_definition -> Psig_class_type ctd
		   | cs:class_specification -> Psig_class cs } -> loc_sig _loc r

  | dol:CHR('$') - e:expression - CHR('$') ->
     let open Quote in
     psig_antiquotation _loc (function
     | Quote_psig -> e
     | _ -> failwith "Bad antiquotation..." (* FIXME:add location *))

let _ = set_grammar signature_item (
  parser
  | e:(alternatives extra_signature) -> attach_sig _loc @ e
  | s:signature_item_base _:double_semi_col? -> attach_sig _loc_s @ [s]
  )

exception Top_Exit

let parser top_phrase =
  | CHR(';')? l:{s:structure_item_base -> s}+ (double_semi_col) -> Ptop_def(l)
  | CHR(';')? EOF -> raise Top_Exit

(*
let _ =
    let (ae,set) = Earley.grammar_info structure_item in
    Charset.(Printf.eprintf "structure_item: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info lident in
    Charset.(Printf.eprintf "lident: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info expression in
    Charset.(Printf.eprintf "expression: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info typexpr in
    Charset.(Printf.eprintf "typexpr: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info let_binding in
    Charset.(Printf.eprintf "let_binding: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info (expression_suit (true,Atom,Top)) in
    Charset.(Printf.eprintf "expression_suit: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info (expression_suit_aux (true,Atom,Top)) in
    Charset.(Printf.eprintf "expression_suit_aux: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info argument in
    Charset.(Printf.eprintf "argument: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info arguments in
    Charset.(Printf.eprintf "arguments: (%b,%a)\n%!" ae print_charset set);
    let (ae,set) = Earley.grammar_info match_cases in
    Charset.(Printf.eprintf "match_cases: (%b,%a)\n%!" ae print_charset set);
*)
end
