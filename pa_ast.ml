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

open Asttypes
open Parsetree
open Longident

let loc_str _loc desc = { pstr_desc = desc; pstr_loc = _loc; }
let loc_sig _loc desc = { psig_desc = desc; psig_loc = _loc; }

#ifversion >= 4.02
#ifversion >= 4.03
let const_string s = Pconst_string(s, None)
#else
let const_string s = Const_string(s, None)
#endif
let loc_expr ?(attributes=[]) _loc e = { pexp_desc = e; pexp_loc = _loc; pexp_attributes = attributes; }
let loc_pat ?(attributes=[]) _loc pat = { ppat_desc = pat; ppat_loc = _loc; ppat_attributes = attributes; }
let loc_pcl ?(attributes=[]) _loc desc = { pcl_desc = desc; pcl_loc = _loc; pcl_attributes = attributes; }
let loc_typ ?(attributes=[]) _loc typ = { ptyp_desc = typ; ptyp_loc = _loc; ptyp_attributes = attributes; }
let pctf_loc ?(attributes=[]) _loc desc = { pctf_desc = desc; pctf_loc = _loc; pctf_attributes = attributes }
let pcty_loc ?(attributes=[]) _loc desc = { pcty_desc = desc; pcty_loc = _loc; pcty_attributes = attributes }
let loc_pcf ?(attributes=[]) _loc desc = { pcf_desc = desc; pcf_loc = _loc; pcf_attributes = attributes }
let mexpr_loc ?(attributes=[]) _loc desc = { pmod_desc = desc; pmod_loc = _loc; pmod_attributes = attributes }
let mtyp_loc ?(attributes=[]) _loc desc = { pmty_desc = desc; pmty_loc = _loc; pmty_attributes = attributes }
let id_loc txt loc = { txt; loc }
let pexp_construct(a,b) = Pexp_construct(a,b)
let pexp_fun(label, opt, pat, expr) =
  Pexp_fun(label,opt,pat,expr)
#else
let const_string s = Const_string(s)
let loc_expr ?(attributes=[]) _loc e = { pexp_desc = e; pexp_loc = _loc; }
let loc_pat ?(attributes=[]) _loc pat = { ppat_desc = pat; ppat_loc = _loc; }
let loc_pcl ?(attributes=[]) _loc desc = { pcl_desc = desc; pcl_loc = _loc }
let loc_typ ?(attributes=[]) _loc typ = { ptyp_desc = typ; ptyp_loc = _loc; }
let loc_pfield ?(attributes=[]) _loc field = { pfield_desc = field; pfield_loc = _loc; }
let pctf_loc ?(attributes=[]) _loc desc = { pctf_desc = desc; pctf_loc = _loc; }
let loc_pcf ?(attributes=[]) _loc desc = { pcf_desc = desc; pcf_loc = _loc; }
let id_loc txt loc = { txt; loc; }
let pcty_loc ?(attributes=[]) _loc desc = { pcty_desc = desc; pcty_loc = _loc; }
let mexpr_loc ?(attributes=[]) _loc desc = { pmod_desc = desc; pmod_loc = _loc }
let mtyp_loc ?(attributes=[]) _loc desc = { pmty_desc = desc; pmty_loc = _loc }
let pexp_construct(a,b) = Pexp_construct(a,b,false)
let pexp_fun(label, opt, pat, expr) =
  Pexp_function(label,opt,[pat,expr])
#endif

let exp_string _loc s = loc_expr _loc (Pexp_constant (const_string s))

#ifversion >= 4.03
let const_float s = Pconst_float(s,None)
let const_char s = Pconst_char(s)
let const_int s = Pconst_integer(string_of_int s,None)
let const_int32 s = Pconst_integer(Int32.to_string s, Some 'l')
let const_int64 s = Pconst_integer(Int64.to_string s, Some 'L')
let const_nativeint s = Pconst_integer(Nativeint.to_string s, Some 'n')
let exp_int _loc i = loc_expr _loc (Pexp_constant (Pconst_integer (string_of_int i,None)))
let exp_char _loc c = loc_expr _loc (Pexp_constant (Pconst_char c))
let exp_float _loc f = loc_expr _loc (Pexp_constant (Pconst_float (f,None)))
let exp_int32 _loc i = loc_expr _loc (Pexp_constant (Pconst_integer (Int32.to_string i,Some 'l')))
let exp_int64 _loc i = loc_expr _loc (Pexp_constant (Pconst_integer (Int64.to_string i,Some 'L')))
let exp_nativeint _loc i = loc_expr _loc (Pexp_constant (Pconst_integer(Nativeint.to_string i,Some 'n')))
#else
let const_float s = Const_float(s)
let const_char s = Const_char(s)
let const_int s = Const_int(s)
let const_int32 s = Const_int32(s)
let const_int64 s = Const_int64(s)
let const_nativeint s = Const_nativeint(s)
let exp_int _loc i = loc_expr _loc (Pexp_constant (Const_int i))
let exp_char _loc c = loc_expr _loc (Pexp_constant (Const_char c))
let exp_float _loc f = loc_expr _loc (Pexp_constant (Const_float f))
let exp_int32 _loc i = loc_expr _loc (Pexp_constant (Const_int32 i))
let exp_int64 _loc i = loc_expr _loc (Pexp_constant (Const_int64 i))
let exp_nativeint _loc i = loc_expr _loc (Pexp_constant (Const_nativeint i))
#endif

let exp_const _loc c es =
  let c = id_loc c _loc in
  loc_expr _loc (pexp_construct(c, es))

let exp_record _loc fs =
  let f (l, e) = (id_loc l _loc, e) in
  let fs = List.map f fs in
  loc_expr _loc (Pexp_record (fs, None))

let exp_None _loc =
  let cnone = id_loc (Lident "None") _loc in
  loc_expr _loc (pexp_construct(cnone, None))

let exp_Some _loc a =
  let csome = id_loc (Lident "Some") _loc in
  loc_expr _loc (pexp_construct(csome, Some a))

let exp_option _loc = function
  | None   -> exp_None _loc
  | Some e -> exp_Some _loc e

let exp_unit _loc =
  let cunit = id_loc (Lident "()") _loc in
  loc_expr _loc (pexp_construct(cunit, None))

let exp_tuple _loc l =
  loc_expr _loc (Pexp_tuple l)

let exp_Nil _loc =
  let cnil = id_loc (Lident "[]") _loc in
  loc_expr _loc (pexp_construct(cnil, None))

let exp_true _loc =
  let ctrue = id_loc (Lident "true") _loc in
  loc_expr _loc (pexp_construct(ctrue, None))

let exp_false _loc =
  let cfalse = id_loc (Lident "false") _loc in
  loc_expr _loc (pexp_construct(cfalse, None))

let exp_bool _loc b =
  if b then exp_true _loc else exp_false _loc

let exp_Cons _loc a l =
  loc_expr _loc (pexp_construct(id_loc (Lident "::") _loc, Some (exp_tuple _loc [a;l])))

let exp_list _loc l =
  List.fold_right (exp_Cons _loc) l (exp_Nil _loc)

let exp_ident _loc id =
  loc_expr _loc (Pexp_ident (id_loc (Lident id) _loc ))

let pat_ident _loc id =
  loc_pat _loc (Ppat_var (id_loc id _loc))

#ifversion >= 4.03
let nolabel = Nolabel
let labelled s = Labelled s
let optional s = Optional s
#else
let nolabel = ""
let labelled s = s
let optional s = "?"^s
#endif

let exp_apply _loc f l =
  loc_expr _loc (Pexp_apply(f, List.map (fun x -> nolabel, x) l))

let exp_Some_fun _loc =
  loc_expr _loc (pexp_fun(nolabel, None, pat_ident _loc "x", (exp_Some _loc (exp_ident _loc "x"))))

let exp_fun _loc id e =
  loc_expr _loc (pexp_fun(nolabel, None, pat_ident _loc id, e))

let exp_lab_apply _loc f l =
  loc_expr _loc (Pexp_apply(f, l))

let exp_app _loc =
  exp_fun _loc "x" (exp_fun _loc "y" (exp_apply _loc (exp_ident _loc "y") [exp_ident _loc "x"]))

let exp_glr_fun _loc f =
  loc_expr _loc (Pexp_ident((id_loc (Ldot(Lident "Decap",f)) _loc) ))

let exp_list_fun _loc f =
  loc_expr _loc (Pexp_ident((id_loc (Ldot(Lident "List",f)) _loc) ))

let exp_str_fun _loc f =
  loc_expr _loc (Pexp_ident((id_loc (Ldot(Lident "Str",f)) _loc) ))

let exp_prelude_fun _loc f =
  loc_expr _loc (Pexp_ident((id_loc (Ldot(Lident "Pa_ocaml_prelude",f)) _loc) ))

let exp_location_fun _loc f =
  loc_expr _loc (Pexp_ident((id_loc (Ldot(Lident "Location",f)) _loc) ))

let exp_Cons_fun _loc =
  exp_fun _loc "x" (exp_fun _loc "l" (exp_Cons _loc (exp_ident _loc "x") (exp_ident _loc "l")))

let exp_Cons_rev_fun _loc =
  exp_fun _loc "x" (exp_fun _loc "l" (exp_Cons _loc (exp_ident _loc "x") (exp_apply _loc (exp_list_fun _loc "rev") [exp_ident _loc "l"])))

let exp_apply_fun _loc =
  exp_fun _loc "a" (exp_fun _loc "f" (exp_apply _loc (exp_ident _loc "f") [exp_ident _loc "a"]))

let ppat_alias _loc p id =
  if id = "_" then p else
    loc_pat _loc (Ppat_alias (p, (id_loc (id) _loc)))

let rec expression_to_pattern p =
  let fn arg = match arg with
    | None -> None
    | Some e -> Some (expression_to_pattern e)
  in
  let p' = match p.pexp_desc with
#ifversion >= 4.00
    | Pexp_ident { txt = Lident id; loc = l } -> Ppat_var { txt = id; loc = l }
#else
    | Pexp_ident(Lident id) -> Ppat_var id
#endif
    | Pexp_constant c -> Ppat_constant c
    | Pexp_tuple l -> Ppat_tuple (List.map expression_to_pattern l)
    | Pexp_array l -> Ppat_array (List.map expression_to_pattern l)
#ifversion >= 4.02
    | Pexp_construct(id, arg) -> Ppat_construct(id, fn arg)
#else
    | Pexp_construct(id, arg, b) -> Ppat_construct(id, fn arg, b)
#endif
    | Pexp_variant(id, arg) -> Ppat_variant(id, fn arg)
    | Pexp_record(l, None) -> Ppat_record(List.map (fun (id, e) -> (id, expression_to_pattern e)) l, Open)
    | Pexp_lazy e -> Ppat_lazy (expression_to_pattern e)
    | Pexp_poly(e, Some ty) -> Ppat_constraint(expression_to_pattern e, ty)
    (* FIXME ? | Pexp_pack of module_expr -> ??? *)
    (* FIXME: a way to produce Ppat_any ??? *)
    (* FIXME: a way to produce Ppat_alias or Ppat_or??? *)
    | _ ->
#ifversion > 4.00
	       Pprintast.expression Format.std_formatter p;
#endif
       failwith "Illegal quotation pattern" (* FIXME: better messages *)
  in
  { ppat_desc = p';
    ppat_loc  = p.pexp_loc;
#ifversion >= 4.02
    ppat_attributes = [];
#endif
  }
