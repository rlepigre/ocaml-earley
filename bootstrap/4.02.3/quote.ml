open Asttypes
open Parsetree
open Longident
open Pa_ast

let anti_table = Hashtbl.create 101

let anti_quotation_key loc = Hashtbl.add anti_table loc (); loc

let is_antiquotation loc = Hashtbl.mem anti_table loc

let loc_ptyp = loc_typ
let loc_ppat = loc_pat
let loc_pexp = loc_expr
let loc_pcty = pcty_loc
let loc_pctf = pctf_loc
let loc_pmty = mtyp_loc
let loc_pmod = mexpr_loc
let loc_psig = loc_sig
let loc_pstr = loc_str

(* Generic functions *)
let quote_bool : Location.t -> bool -> expression =
  Pa_ast.exp_bool

let quote_int : Location.t -> int -> expression =
  Pa_ast.exp_int

let quote_char : Location.t -> char -> expression =
  Pa_ast.exp_char

let quote_string : Location.t -> string -> expression =
  Pa_ast.exp_string

let quote_int32 : Location.t -> int32 -> expression =
  Pa_ast.exp_int32

let quote_int64 : Location.t -> int64 -> expression =
  Pa_ast.exp_int64

let quote_nativeint : Location.t -> nativeint -> expression =
  Pa_ast.exp_nativeint

let quote_option : 'a. (Location.t -> 'a -> expression) -> Location.t -> 'a option -> expression =
  fun qe _loc eo ->
    let e =
      match eo with
      | None   -> None
      | Some e -> Some (qe _loc e)
    in Pa_ast.exp_option _loc e

let quote_list : 'a. (Location.t -> 'a -> expression) -> Location.t -> 'a list -> expression =
  fun qe _loc el ->
    let el = List.map (qe _loc) el in
    Pa_ast.exp_list _loc el

let quote_tuple : Location.t -> expression list -> expression =
  Pa_ast.exp_tuple

let quote_const : Location.t -> Longident.t -> expression list -> expression =
  (fun _loc s l ->
    match l with [] -> Pa_ast.exp_const _loc s None
                | [x] -> Pa_ast.exp_const _loc s (Some x)
                | l -> Pa_ast.exp_const _loc s (Some (Pa_ast.exp_tuple _loc l)))

let lexing s = Ldot(Lident "Lexing", s)
let location s = Ldot(Lident "Location", s)
let longident s = Ldot(Lident "Longident", s)

let rec quote_longident : Location.t -> Longident.t -> expression =
  fun _loc l ->
    match l with
    | Lident s       -> let s = quote_string _loc s in
                        quote_const _loc (longident "Lident") [s]
    | Ldot (l, s)    -> let l = quote_longident _loc l in
                        let s = quote_string _loc s in
                        quote_const _loc (longident "Ldot") [l; s]
    | Lapply (l, l') -> let l = quote_longident _loc l in
                        let l' = quote_longident _loc l' in
                        quote_const _loc (longident "Lapply") [l; l']

let quote_record : Location.t -> (Longident.t * expression) list -> expression =
  Pa_ast.exp_record

let quote_position : Location.t -> Lexing.position -> expression =
  (fun _loc {Lexing.pos_fname = pfn; Lexing.pos_lnum = ln; Lexing.pos_bol = bl; Lexing.pos_cnum = pcn} ->
    let pfn = quote_string _loc pfn in
    let ln  = quote_int _loc ln in
    let bl  = quote_int _loc bl in
    let pcn = quote_int _loc pcn in
    quote_record _loc
      [(lexing "pos_fname",pfn); (lexing "pos_lnum",ln); (lexing "pos_bol",bl); (lexing "pos_cnum",pcn)])

let quote_location_t : Location.t -> Location.t -> expression =
  (fun _loc {Location.loc_start = ls; Location.loc_end = le; Location.loc_ghost = g} ->
    let ls = quote_position _loc ls in
    let le = quote_position _loc le in
    let g  = quote_bool _loc g in
    quote_record _loc [(location "loc_start",ls); (location "loc_end",le); (location "loc_ghost",g)])
(* asttypes.mli *)
let quote_constant _loc x = match x with
  | Const_int(x) -> quote_const _loc (Ldot(Lident "Asttypes", "Const_int")) [quote_int _loc x]
  | Const_char(x) -> quote_const _loc (Ldot(Lident "Asttypes", "Const_char")) [quote_char _loc x]
  | Const_string(x1,x2) -> quote_const _loc (Ldot(Lident "Asttypes", "Const_string")) [ quote_string _loc x1; (quote_option quote_string) _loc x2;]
  | Const_float(x) -> quote_const _loc (Ldot(Lident "Asttypes", "Const_float")) [quote_string _loc x]
  | Const_int32(x) -> quote_const _loc (Ldot(Lident "Asttypes", "Const_int32")) [quote_int32 _loc x]
  | Const_int64(x) -> quote_const _loc (Ldot(Lident "Asttypes", "Const_int64")) [quote_int64 _loc x]
  | Const_nativeint(x) -> quote_const _loc (Ldot(Lident "Asttypes", "Const_nativeint")) [quote_nativeint _loc x]

let quote_rec_flag _loc x = match x with
  | Nonrecursive -> quote_const _loc (Ldot(Lident "Asttypes", "Nonrecursive")) []
  | Recursive -> quote_const _loc (Ldot(Lident "Asttypes", "Recursive")) []

let quote_direction_flag _loc x = match x with
  | Upto -> quote_const _loc (Ldot(Lident "Asttypes", "Upto")) []
  | Downto -> quote_const _loc (Ldot(Lident "Asttypes", "Downto")) []

let quote_private_flag _loc x = match x with
  | Private -> quote_const _loc (Ldot(Lident "Asttypes", "Private")) []
  | Public -> quote_const _loc (Ldot(Lident "Asttypes", "Public")) []

let quote_mutable_flag _loc x = match x with
  | Immutable -> quote_const _loc (Ldot(Lident "Asttypes", "Immutable")) []
  | Mutable -> quote_const _loc (Ldot(Lident "Asttypes", "Mutable")) []

let quote_virtual_flag _loc x = match x with
  | Virtual -> quote_const _loc (Ldot(Lident "Asttypes", "Virtual")) []
  | Concrete -> quote_const _loc (Ldot(Lident "Asttypes", "Concrete")) []

let quote_override_flag _loc x = match x with
  | Override -> quote_const _loc (Ldot(Lident "Asttypes", "Override")) []
  | Fresh -> quote_const _loc (Ldot(Lident "Asttypes", "Fresh")) []

let quote_closed_flag _loc x = match x with
  | Closed -> quote_const _loc (Ldot(Lident "Asttypes", "Closed")) []
  | Open -> quote_const _loc (Ldot(Lident "Asttypes", "Open")) []

let quote_label _loc x =  quote_string _loc x
let quote_loc : 'a. (Location.t -> 'a -> expression) -> Location.t -> 'a loc -> expression =
  fun quote_a _loc r -> 
    quote_record _loc [
   ((Ldot(Lident "Asttypes", "txt")), quote_a _loc r.txt) ;
   ((Ldot(Lident "Asttypes", "loc")), quote_location_t _loc r.loc) ;
  ]

let quote_variance _loc x = match x with
  | Covariant -> quote_const _loc (Ldot(Lident "Asttypes", "Covariant")) []
  | Contravariant -> quote_const _loc (Ldot(Lident "Asttypes", "Contravariant")) []
  | Invariant -> quote_const _loc (Ldot(Lident "Asttypes", "Invariant")) []


(* parsetree.mli *)
let rec quote_attribute _loc x =  (fun _loc (x1,x2) -> quote_tuple _loc [(quote_loc quote_string) _loc x1;quote_payload _loc x2;]) _loc x
and quote_extension _loc x =  (fun _loc (x1,x2) -> quote_tuple _loc [(quote_loc quote_string) _loc x1;quote_payload _loc x2;]) _loc x
and quote_attributes _loc x =  (quote_list quote_attribute) _loc x
and quote_payload _loc x = match x with
  | PStr(x) -> quote_const _loc (Ldot(Lident "Parsetree", "PStr")) [quote_structure _loc x]
  | PTyp(x) -> quote_const _loc (Ldot(Lident "Parsetree", "PTyp")) [quote_core_type _loc x]
  | PPat(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "PPat")) [ quote_pattern _loc x1; (quote_option quote_expression) _loc x2;]

and quote_core_type _loc r = if is_antiquotation r.ptyp_loc then loc_expr r.ptyp_loc (Obj.magic r.ptyp_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "ptyp_desc")), quote_core_type_desc _loc r.ptyp_desc) ;
   ((Ldot(Lident "Parsetree", "ptyp_loc")), quote_location_t _loc r.ptyp_loc) ;
   ((Ldot(Lident "Parsetree", "ptyp_attributes")), quote_attributes _loc r.ptyp_attributes) ;
  ]
and ptyp_antiquotation e = loc_ptyp (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_core_type_desc _loc x = match x with
  | Ptyp_any -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_any")) []
  | Ptyp_var(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_var")) [quote_string _loc x]
  | Ptyp_arrow(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_arrow")) [ quote_label _loc x1; quote_core_type _loc x2; quote_core_type _loc x3;]
  | Ptyp_tuple(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_tuple")) [(quote_list quote_core_type) _loc x]
  | Ptyp_constr(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_constr")) [ (quote_loc quote_longident) _loc x1; (quote_list quote_core_type) _loc x2;]
  | Ptyp_object(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_object")) [ (quote_list (fun _loc (x1,x2,x3) -> quote_tuple _loc [quote_string _loc x1;quote_attributes _loc x2;quote_core_type _loc x3;])) _loc x1; quote_closed_flag _loc x2;]
  | Ptyp_class(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_class")) [ (quote_loc quote_longident) _loc x1; (quote_list quote_core_type) _loc x2;]
  | Ptyp_alias(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_alias")) [ quote_core_type _loc x1; quote_string _loc x2;]
  | Ptyp_variant(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_variant")) [ (quote_list quote_row_field) _loc x1; quote_closed_flag _loc x2; (quote_option (quote_list quote_label)) _loc x3;]
  | Ptyp_poly(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_poly")) [ (quote_list quote_string) _loc x1; quote_core_type _loc x2;]
  | Ptyp_package(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_package")) [quote_package_type _loc x]
  | Ptyp_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptyp_extension")) [quote_extension _loc x]

and quote_package_type _loc x =  (fun _loc (x1,x2) -> quote_tuple _loc [(quote_loc quote_longident) _loc x1;(quote_list (fun _loc (x1,x2) -> quote_tuple _loc [(quote_loc quote_longident) _loc x1;quote_core_type _loc x2;])) _loc x2;]) _loc x
and quote_row_field _loc x = match x with
  | Rtag(x1,x2,x3,x4) -> quote_const _loc (Ldot(Lident "Parsetree", "Rtag")) [ quote_label _loc x1; quote_attributes _loc x2; quote_bool _loc x3; (quote_list quote_core_type) _loc x4;]
  | Rinherit(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Rinherit")) [quote_core_type _loc x]

and quote_pattern _loc r = if is_antiquotation r.ppat_loc then loc_expr r.ppat_loc (Obj.magic r.ppat_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "ppat_desc")), quote_pattern_desc _loc r.ppat_desc) ;
   ((Ldot(Lident "Parsetree", "ppat_loc")), quote_location_t _loc r.ppat_loc) ;
   ((Ldot(Lident "Parsetree", "ppat_attributes")), quote_attributes _loc r.ppat_attributes) ;
  ]
and ppat_antiquotation e = loc_ppat (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_pattern_desc _loc x = match x with
  | Ppat_any -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_any")) []
  | Ppat_var(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_var")) [(quote_loc quote_string) _loc x]
  | Ppat_alias(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_alias")) [ quote_pattern _loc x1; (quote_loc quote_string) _loc x2;]
  | Ppat_constant(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_constant")) [quote_constant _loc x]
  | Ppat_interval(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_interval")) [ quote_constant _loc x1; quote_constant _loc x2;]
  | Ppat_tuple(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_tuple")) [(quote_list quote_pattern) _loc x]
  | Ppat_construct(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_construct")) [ (quote_loc quote_longident) _loc x1; (quote_option quote_pattern) _loc x2;]
  | Ppat_variant(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_variant")) [ quote_label _loc x1; (quote_option quote_pattern) _loc x2;]
  | Ppat_record(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_record")) [ (quote_list (fun _loc (x1,x2) -> quote_tuple _loc [(quote_loc quote_longident) _loc x1;quote_pattern _loc x2;])) _loc x1; quote_closed_flag _loc x2;]
  | Ppat_array(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_array")) [(quote_list quote_pattern) _loc x]
  | Ppat_or(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_or")) [ quote_pattern _loc x1; quote_pattern _loc x2;]
  | Ppat_constraint(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_constraint")) [ quote_pattern _loc x1; quote_core_type _loc x2;]
  | Ppat_type(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_type")) [(quote_loc quote_longident) _loc x]
  | Ppat_lazy(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_lazy")) [quote_pattern _loc x]
  | Ppat_unpack(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_unpack")) [(quote_loc quote_string) _loc x]
  | Ppat_exception(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_exception")) [quote_pattern _loc x]
  | Ppat_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ppat_extension")) [quote_extension _loc x]

and quote_expression _loc r = if is_antiquotation r.pexp_loc then loc_expr r.pexp_loc (Obj.magic r.pexp_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pexp_desc")), quote_expression_desc _loc r.pexp_desc) ;
   ((Ldot(Lident "Parsetree", "pexp_loc")), quote_location_t _loc r.pexp_loc) ;
   ((Ldot(Lident "Parsetree", "pexp_attributes")), quote_attributes _loc r.pexp_attributes) ;
  ]
and pexp_antiquotation e = loc_pexp (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_expression_desc _loc x = match x with
  | Pexp_ident(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_ident")) [(quote_loc quote_longident) _loc x]
  | Pexp_constant(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_constant")) [quote_constant _loc x]
  | Pexp_let(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_let")) [ quote_rec_flag _loc x1; (quote_list quote_value_binding) _loc x2; quote_expression _loc x3;]
  | Pexp_function(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_function")) [(quote_list quote_case) _loc x]
  | Pexp_fun(x1,x2,x3,x4) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_fun")) [ quote_label _loc x1; (quote_option quote_expression) _loc x2; quote_pattern _loc x3; quote_expression _loc x4;]
  | Pexp_apply(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_apply")) [ quote_expression _loc x1; (quote_list (fun _loc (x1,x2) -> quote_tuple _loc [quote_label _loc x1;quote_expression _loc x2;])) _loc x2;]
  | Pexp_match(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_match")) [ quote_expression _loc x1; (quote_list quote_case) _loc x2;]
  | Pexp_try(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_try")) [ quote_expression _loc x1; (quote_list quote_case) _loc x2;]
  | Pexp_tuple(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_tuple")) [(quote_list quote_expression) _loc x]
  | Pexp_construct(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_construct")) [ (quote_loc quote_longident) _loc x1; (quote_option quote_expression) _loc x2;]
  | Pexp_variant(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_variant")) [ quote_label _loc x1; (quote_option quote_expression) _loc x2;]
  | Pexp_record(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_record")) [ (quote_list (fun _loc (x1,x2) -> quote_tuple _loc [(quote_loc quote_longident) _loc x1;quote_expression _loc x2;])) _loc x1; (quote_option quote_expression) _loc x2;]
  | Pexp_field(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_field")) [ quote_expression _loc x1; (quote_loc quote_longident) _loc x2;]
  | Pexp_setfield(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_setfield")) [ quote_expression _loc x1; (quote_loc quote_longident) _loc x2; quote_expression _loc x3;]
  | Pexp_array(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_array")) [(quote_list quote_expression) _loc x]
  | Pexp_ifthenelse(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_ifthenelse")) [ quote_expression _loc x1; quote_expression _loc x2; (quote_option quote_expression) _loc x3;]
  | Pexp_sequence(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_sequence")) [ quote_expression _loc x1; quote_expression _loc x2;]
  | Pexp_while(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_while")) [ quote_expression _loc x1; quote_expression _loc x2;]
  | Pexp_for(x1,x2,x3,x4,x5) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_for")) [ quote_pattern _loc x1; quote_expression _loc x2; quote_expression _loc x3; quote_direction_flag _loc x4; quote_expression _loc x5;]
  | Pexp_constraint(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_constraint")) [ quote_expression _loc x1; quote_core_type _loc x2;]
  | Pexp_coerce(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_coerce")) [ quote_expression _loc x1; (quote_option quote_core_type) _loc x2; quote_core_type _loc x3;]
  | Pexp_send(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_send")) [ quote_expression _loc x1; quote_string _loc x2;]
  | Pexp_new(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_new")) [(quote_loc quote_longident) _loc x]
  | Pexp_setinstvar(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_setinstvar")) [ (quote_loc quote_string) _loc x1; quote_expression _loc x2;]
  | Pexp_override(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_override")) [(quote_list (fun _loc (x1,x2) -> quote_tuple _loc [(quote_loc quote_string) _loc x1;quote_expression _loc x2;])) _loc x]
  | Pexp_letmodule(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_letmodule")) [ (quote_loc quote_string) _loc x1; quote_module_expr _loc x2; quote_expression _loc x3;]
  | Pexp_assert(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_assert")) [quote_expression _loc x]
  | Pexp_lazy(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_lazy")) [quote_expression _loc x]
  | Pexp_poly(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_poly")) [ quote_expression _loc x1; (quote_option quote_core_type) _loc x2;]
  | Pexp_object(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_object")) [quote_class_structure _loc x]
  | Pexp_newtype(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_newtype")) [ quote_string _loc x1; quote_expression _loc x2;]
  | Pexp_pack(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_pack")) [quote_module_expr _loc x]
  | Pexp_open(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_open")) [ quote_override_flag _loc x1; (quote_loc quote_longident) _loc x2; quote_expression _loc x3;]
  | Pexp_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pexp_extension")) [quote_extension _loc x]

and quote_case _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pc_lhs")), quote_pattern _loc r.pc_lhs) ;
   ((Ldot(Lident "Parsetree", "pc_guard")), (quote_option quote_expression) _loc r.pc_guard) ;
   ((Ldot(Lident "Parsetree", "pc_rhs")), quote_expression _loc r.pc_rhs) ;
  ]

and quote_value_description _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pval_name")), (quote_loc quote_string) _loc r.pval_name) ;
   ((Ldot(Lident "Parsetree", "pval_type")), quote_core_type _loc r.pval_type) ;
   ((Ldot(Lident "Parsetree", "pval_prim")), (quote_list quote_string) _loc r.pval_prim) ;
   ((Ldot(Lident "Parsetree", "pval_attributes")), quote_attributes _loc r.pval_attributes) ;
   ((Ldot(Lident "Parsetree", "pval_loc")), quote_location_t _loc r.pval_loc) ;
  ]

and quote_type_declaration _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "ptype_name")), (quote_loc quote_string) _loc r.ptype_name) ;
   ((Ldot(Lident "Parsetree", "ptype_params")), (quote_list (fun _loc (x1,x2) -> quote_tuple _loc [quote_core_type _loc x1;quote_variance _loc x2;])) _loc r.ptype_params) ;
   ((Ldot(Lident "Parsetree", "ptype_cstrs")), (quote_list (fun _loc (x1,x2,x3) -> quote_tuple _loc [quote_core_type _loc x1;quote_core_type _loc x2;quote_location_t _loc x3;])) _loc r.ptype_cstrs) ;
   ((Ldot(Lident "Parsetree", "ptype_kind")), quote_type_kind _loc r.ptype_kind) ;
   ((Ldot(Lident "Parsetree", "ptype_private")), quote_private_flag _loc r.ptype_private) ;
   ((Ldot(Lident "Parsetree", "ptype_manifest")), (quote_option quote_core_type) _loc r.ptype_manifest) ;
   ((Ldot(Lident "Parsetree", "ptype_attributes")), quote_attributes _loc r.ptype_attributes) ;
   ((Ldot(Lident "Parsetree", "ptype_loc")), quote_location_t _loc r.ptype_loc) ;
  ]

and quote_type_kind _loc x = match x with
  | Ptype_abstract -> quote_const _loc (Ldot(Lident "Parsetree", "Ptype_abstract")) []
  | Ptype_variant(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptype_variant")) [(quote_list quote_constructor_declaration) _loc x]
  | Ptype_record(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptype_record")) [(quote_list quote_label_declaration) _loc x]
  | Ptype_open -> quote_const _loc (Ldot(Lident "Parsetree", "Ptype_open")) []

and quote_label_declaration _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pld_name")), (quote_loc quote_string) _loc r.pld_name) ;
   ((Ldot(Lident "Parsetree", "pld_mutable")), quote_mutable_flag _loc r.pld_mutable) ;
   ((Ldot(Lident "Parsetree", "pld_type")), quote_core_type _loc r.pld_type) ;
   ((Ldot(Lident "Parsetree", "pld_loc")), quote_location_t _loc r.pld_loc) ;
   ((Ldot(Lident "Parsetree", "pld_attributes")), quote_attributes _loc r.pld_attributes) ;
  ]

and quote_constructor_declaration _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pcd_name")), (quote_loc quote_string) _loc r.pcd_name) ;
   ((Ldot(Lident "Parsetree", "pcd_args")), (quote_list quote_core_type) _loc r.pcd_args) ;
   ((Ldot(Lident "Parsetree", "pcd_res")), (quote_option quote_core_type) _loc r.pcd_res) ;
   ((Ldot(Lident "Parsetree", "pcd_loc")), quote_location_t _loc r.pcd_loc) ;
   ((Ldot(Lident "Parsetree", "pcd_attributes")), quote_attributes _loc r.pcd_attributes) ;
  ]

and quote_type_extension _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "ptyext_path")), (quote_loc quote_longident) _loc r.ptyext_path) ;
   ((Ldot(Lident "Parsetree", "ptyext_params")), (quote_list (fun _loc (x1,x2) -> quote_tuple _loc [quote_core_type _loc x1;quote_variance _loc x2;])) _loc r.ptyext_params) ;
   ((Ldot(Lident "Parsetree", "ptyext_constructors")), (quote_list quote_extension_constructor) _loc r.ptyext_constructors) ;
   ((Ldot(Lident "Parsetree", "ptyext_private")), quote_private_flag _loc r.ptyext_private) ;
   ((Ldot(Lident "Parsetree", "ptyext_attributes")), quote_attributes _loc r.ptyext_attributes) ;
  ]

and quote_extension_constructor _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pext_name")), (quote_loc quote_string) _loc r.pext_name) ;
   ((Ldot(Lident "Parsetree", "pext_kind")), quote_extension_constructor_kind _loc r.pext_kind) ;
   ((Ldot(Lident "Parsetree", "pext_loc")), quote_location_t _loc r.pext_loc) ;
   ((Ldot(Lident "Parsetree", "pext_attributes")), quote_attributes _loc r.pext_attributes) ;
  ]

and quote_extension_constructor_kind _loc x = match x with
  | Pext_decl(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pext_decl")) [ (quote_list quote_core_type) _loc x1; (quote_option quote_core_type) _loc x2;]
  | Pext_rebind(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pext_rebind")) [(quote_loc quote_longident) _loc x]

and quote_class_type _loc r = if is_antiquotation r.pcty_loc then loc_expr r.pcty_loc (Obj.magic r.pcty_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pcty_desc")), quote_class_type_desc _loc r.pcty_desc) ;
   ((Ldot(Lident "Parsetree", "pcty_loc")), quote_location_t _loc r.pcty_loc) ;
   ((Ldot(Lident "Parsetree", "pcty_attributes")), quote_attributes _loc r.pcty_attributes) ;
  ]
and pcty_antiquotation e = loc_pcty (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_class_type_desc _loc x = match x with
  | Pcty_constr(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcty_constr")) [ (quote_loc quote_longident) _loc x1; (quote_list quote_core_type) _loc x2;]
  | Pcty_signature(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcty_signature")) [quote_class_signature _loc x]
  | Pcty_arrow(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcty_arrow")) [ quote_label _loc x1; quote_core_type _loc x2; quote_class_type _loc x3;]
  | Pcty_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcty_extension")) [quote_extension _loc x]

and quote_class_signature _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pcsig_self")), quote_core_type _loc r.pcsig_self) ;
   ((Ldot(Lident "Parsetree", "pcsig_fields")), (quote_list quote_class_type_field) _loc r.pcsig_fields) ;
  ]

and quote_class_type_field _loc r = if is_antiquotation r.pctf_loc then loc_expr r.pctf_loc (Obj.magic r.pctf_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pctf_desc")), quote_class_type_field_desc _loc r.pctf_desc) ;
   ((Ldot(Lident "Parsetree", "pctf_loc")), quote_location_t _loc r.pctf_loc) ;
   ((Ldot(Lident "Parsetree", "pctf_attributes")), quote_attributes _loc r.pctf_attributes) ;
  ]
and pctf_antiquotation e = loc_pctf (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_class_type_field_desc _loc x = match x with
  | Pctf_inherit(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pctf_inherit")) [quote_class_type _loc x]
  | Pctf_val(x1,x2,x3,x4) -> quote_const _loc (Ldot(Lident "Parsetree", "Pctf_val")) [ quote_string _loc x1; quote_mutable_flag _loc x2; quote_virtual_flag _loc x3; quote_core_type _loc x4;]
  | Pctf_method(x1,x2,x3,x4) -> quote_const _loc (Ldot(Lident "Parsetree", "Pctf_method")) [ quote_string _loc x1; quote_private_flag _loc x2; quote_virtual_flag _loc x3; quote_core_type _loc x4;]
  | Pctf_constraint(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pctf_constraint")) [ quote_core_type _loc x1; quote_core_type _loc x2;]
  | Pctf_attribute(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pctf_attribute")) [quote_attribute _loc x]
  | Pctf_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pctf_extension")) [quote_extension _loc x]

and quote_class_infos : 'a. (Location.t -> 'a -> expression) -> Location.t -> 'a class_infos -> expression =
  fun quote_a _loc r -> 
    quote_record _loc [
   ((Ldot(Lident "Parsetree", "pci_virt")), quote_virtual_flag _loc r.pci_virt) ;
   ((Ldot(Lident "Parsetree", "pci_params")), (quote_list (fun _loc (x1,x2) -> quote_tuple _loc [quote_core_type _loc x1;quote_variance _loc x2;])) _loc r.pci_params) ;
   ((Ldot(Lident "Parsetree", "pci_name")), (quote_loc quote_string) _loc r.pci_name) ;
   ((Ldot(Lident "Parsetree", "pci_expr")), quote_a _loc r.pci_expr) ;
   ((Ldot(Lident "Parsetree", "pci_loc")), quote_location_t _loc r.pci_loc) ;
   ((Ldot(Lident "Parsetree", "pci_attributes")), quote_attributes _loc r.pci_attributes) ;
  ]

and quote_class_description _loc x =  (quote_class_infos quote_class_type) _loc x
and quote_class_type_declaration _loc x =  (quote_class_infos quote_class_type) _loc x
and quote_class_expr _loc r = if is_antiquotation r.pcl_loc then loc_expr r.pcl_loc (Obj.magic r.pcl_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pcl_desc")), quote_class_expr_desc _loc r.pcl_desc) ;
   ((Ldot(Lident "Parsetree", "pcl_loc")), quote_location_t _loc r.pcl_loc) ;
   ((Ldot(Lident "Parsetree", "pcl_attributes")), quote_attributes _loc r.pcl_attributes) ;
  ]
and pcl_antiquotation e = loc_pcl (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_class_expr_desc _loc x = match x with
  | Pcl_constr(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcl_constr")) [ (quote_loc quote_longident) _loc x1; (quote_list quote_core_type) _loc x2;]
  | Pcl_structure(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcl_structure")) [quote_class_structure _loc x]
  | Pcl_fun(x1,x2,x3,x4) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcl_fun")) [ quote_label _loc x1; (quote_option quote_expression) _loc x2; quote_pattern _loc x3; quote_class_expr _loc x4;]
  | Pcl_apply(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcl_apply")) [ quote_class_expr _loc x1; (quote_list (fun _loc (x1,x2) -> quote_tuple _loc [quote_label _loc x1;quote_expression _loc x2;])) _loc x2;]
  | Pcl_let(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcl_let")) [ quote_rec_flag _loc x1; (quote_list quote_value_binding) _loc x2; quote_class_expr _loc x3;]
  | Pcl_constraint(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcl_constraint")) [ quote_class_expr _loc x1; quote_class_type _loc x2;]
  | Pcl_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcl_extension")) [quote_extension _loc x]

and quote_class_structure _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pcstr_self")), quote_pattern _loc r.pcstr_self) ;
   ((Ldot(Lident "Parsetree", "pcstr_fields")), (quote_list quote_class_field) _loc r.pcstr_fields) ;
  ]

and quote_class_field _loc r = if is_antiquotation r.pcf_loc then loc_expr r.pcf_loc (Obj.magic r.pcf_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pcf_desc")), quote_class_field_desc _loc r.pcf_desc) ;
   ((Ldot(Lident "Parsetree", "pcf_loc")), quote_location_t _loc r.pcf_loc) ;
   ((Ldot(Lident "Parsetree", "pcf_attributes")), quote_attributes _loc r.pcf_attributes) ;
  ]
and pcf_antiquotation e = loc_pcf (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_class_field_desc _loc x = match x with
  | Pcf_inherit(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcf_inherit")) [ quote_override_flag _loc x1; quote_class_expr _loc x2; (quote_option quote_string) _loc x3;]
  | Pcf_val(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcf_val")) [ (quote_loc quote_string) _loc x1; quote_mutable_flag _loc x2; quote_class_field_kind _loc x3;]
  | Pcf_method(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcf_method")) [ (quote_loc quote_string) _loc x1; quote_private_flag _loc x2; quote_class_field_kind _loc x3;]
  | Pcf_constraint(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcf_constraint")) [ quote_core_type _loc x1; quote_core_type _loc x2;]
  | Pcf_initializer(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcf_initializer")) [quote_expression _loc x]
  | Pcf_attribute(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcf_attribute")) [quote_attribute _loc x]
  | Pcf_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pcf_extension")) [quote_extension _loc x]

and quote_class_field_kind _loc x = match x with
  | Cfk_virtual(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Cfk_virtual")) [quote_core_type _loc x]
  | Cfk_concrete(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Cfk_concrete")) [ quote_override_flag _loc x1; quote_expression _loc x2;]

and quote_class_declaration _loc x =  (quote_class_infos quote_class_expr) _loc x
and quote_module_type _loc r = if is_antiquotation r.pmty_loc then loc_expr r.pmty_loc (Obj.magic r.pmty_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pmty_desc")), quote_module_type_desc _loc r.pmty_desc) ;
   ((Ldot(Lident "Parsetree", "pmty_loc")), quote_location_t _loc r.pmty_loc) ;
   ((Ldot(Lident "Parsetree", "pmty_attributes")), quote_attributes _loc r.pmty_attributes) ;
  ]
and pmty_antiquotation e = loc_pmty (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_module_type_desc _loc x = match x with
  | Pmty_ident(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmty_ident")) [(quote_loc quote_longident) _loc x]
  | Pmty_signature(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmty_signature")) [quote_signature _loc x]
  | Pmty_functor(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmty_functor")) [ (quote_loc quote_string) _loc x1; (quote_option quote_module_type) _loc x2; quote_module_type _loc x3;]
  | Pmty_with(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmty_with")) [ quote_module_type _loc x1; (quote_list quote_with_constraint) _loc x2;]
  | Pmty_typeof(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmty_typeof")) [quote_module_expr _loc x]
  | Pmty_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmty_extension")) [quote_extension _loc x]
  | Pmty_alias(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmty_alias")) [(quote_loc quote_longident) _loc x]

and quote_signature _loc x =  (quote_list quote_signature_item) _loc x
and quote_signature_item _loc r = if is_antiquotation r.psig_loc then loc_expr r.psig_loc (Obj.magic r.psig_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "psig_desc")), quote_signature_item_desc _loc r.psig_desc) ;
   ((Ldot(Lident "Parsetree", "psig_loc")), quote_location_t _loc r.psig_loc) ;
  ]
and psig_antiquotation e = loc_psig (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_signature_item_desc _loc x = match x with
  | Psig_value(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_value")) [quote_value_description _loc x]
  | Psig_type(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_type")) [(quote_list quote_type_declaration) _loc x]
  | Psig_typext(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_typext")) [quote_type_extension _loc x]
  | Psig_exception(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_exception")) [quote_extension_constructor _loc x]
  | Psig_module(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_module")) [quote_module_declaration _loc x]
  | Psig_recmodule(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_recmodule")) [(quote_list quote_module_declaration) _loc x]
  | Psig_modtype(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_modtype")) [quote_module_type_declaration _loc x]
  | Psig_open(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_open")) [quote_open_description _loc x]
  | Psig_include(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_include")) [quote_include_description _loc x]
  | Psig_class(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_class")) [(quote_list quote_class_description) _loc x]
  | Psig_class_type(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_class_type")) [(quote_list quote_class_type_declaration) _loc x]
  | Psig_attribute(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_attribute")) [quote_attribute _loc x]
  | Psig_extension(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Psig_extension")) [ quote_extension _loc x1; quote_attributes _loc x2;]

and quote_module_declaration _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pmd_name")), (quote_loc quote_string) _loc r.pmd_name) ;
   ((Ldot(Lident "Parsetree", "pmd_type")), quote_module_type _loc r.pmd_type) ;
   ((Ldot(Lident "Parsetree", "pmd_attributes")), quote_attributes _loc r.pmd_attributes) ;
   ((Ldot(Lident "Parsetree", "pmd_loc")), quote_location_t _loc r.pmd_loc) ;
  ]

and quote_module_type_declaration _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pmtd_name")), (quote_loc quote_string) _loc r.pmtd_name) ;
   ((Ldot(Lident "Parsetree", "pmtd_type")), (quote_option quote_module_type) _loc r.pmtd_type) ;
   ((Ldot(Lident "Parsetree", "pmtd_attributes")), quote_attributes _loc r.pmtd_attributes) ;
   ((Ldot(Lident "Parsetree", "pmtd_loc")), quote_location_t _loc r.pmtd_loc) ;
  ]

and quote_open_description _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "popen_lid")), (quote_loc quote_longident) _loc r.popen_lid) ;
   ((Ldot(Lident "Parsetree", "popen_override")), quote_override_flag _loc r.popen_override) ;
   ((Ldot(Lident "Parsetree", "popen_loc")), quote_location_t _loc r.popen_loc) ;
   ((Ldot(Lident "Parsetree", "popen_attributes")), quote_attributes _loc r.popen_attributes) ;
  ]

and quote_include_infos : 'a. (Location.t -> 'a -> expression) -> Location.t -> 'a include_infos -> expression =
  fun quote_a _loc r -> 
    quote_record _loc [
   ((Ldot(Lident "Parsetree", "pincl_mod")), quote_a _loc r.pincl_mod) ;
   ((Ldot(Lident "Parsetree", "pincl_loc")), quote_location_t _loc r.pincl_loc) ;
   ((Ldot(Lident "Parsetree", "pincl_attributes")), quote_attributes _loc r.pincl_attributes) ;
  ]

and quote_include_description _loc x =  (quote_include_infos quote_module_type) _loc x
and quote_include_declaration _loc x =  (quote_include_infos quote_module_expr) _loc x
and quote_with_constraint _loc x = match x with
  | Pwith_type(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pwith_type")) [ (quote_loc quote_longident) _loc x1; quote_type_declaration _loc x2;]
  | Pwith_module(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pwith_module")) [ (quote_loc quote_longident) _loc x1; (quote_loc quote_longident) _loc x2;]
  | Pwith_typesubst(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pwith_typesubst")) [quote_type_declaration _loc x]
  | Pwith_modsubst(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pwith_modsubst")) [ (quote_loc quote_string) _loc x1; (quote_loc quote_longident) _loc x2;]

and quote_module_expr _loc r = if is_antiquotation r.pmod_loc then loc_expr r.pmod_loc (Obj.magic r.pmod_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pmod_desc")), quote_module_expr_desc _loc r.pmod_desc) ;
   ((Ldot(Lident "Parsetree", "pmod_loc")), quote_location_t _loc r.pmod_loc) ;
   ((Ldot(Lident "Parsetree", "pmod_attributes")), quote_attributes _loc r.pmod_attributes) ;
  ]
and pmod_antiquotation e = loc_pmod (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_module_expr_desc _loc x = match x with
  | Pmod_ident(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmod_ident")) [(quote_loc quote_longident) _loc x]
  | Pmod_structure(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmod_structure")) [quote_structure _loc x]
  | Pmod_functor(x1,x2,x3) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmod_functor")) [ (quote_loc quote_string) _loc x1; (quote_option quote_module_type) _loc x2; quote_module_expr _loc x3;]
  | Pmod_apply(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmod_apply")) [ quote_module_expr _loc x1; quote_module_expr _loc x2;]
  | Pmod_constraint(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmod_constraint")) [ quote_module_expr _loc x1; quote_module_type _loc x2;]
  | Pmod_unpack(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmod_unpack")) [quote_expression _loc x]
  | Pmod_extension(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pmod_extension")) [quote_extension _loc x]

and quote_structure _loc x =  (quote_list quote_structure_item) _loc x
and quote_structure_item _loc r = if is_antiquotation r.pstr_loc then loc_expr r.pstr_loc (Obj.magic r.pstr_desc) else   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pstr_desc")), quote_structure_item_desc _loc r.pstr_desc) ;
   ((Ldot(Lident "Parsetree", "pstr_loc")), quote_location_t _loc r.pstr_loc) ;
  ]
and pstr_antiquotation e = loc_pstr (anti_quotation_key e.pexp_loc) (Obj.magic e.pexp_desc)
and quote_structure_item_desc _loc x = match x with
  | Pstr_eval(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_eval")) [ quote_expression _loc x1; quote_attributes _loc x2;]
  | Pstr_value(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_value")) [ quote_rec_flag _loc x1; (quote_list quote_value_binding) _loc x2;]
  | Pstr_primitive(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_primitive")) [quote_value_description _loc x]
  | Pstr_type(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_type")) [(quote_list quote_type_declaration) _loc x]
  | Pstr_typext(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_typext")) [quote_type_extension _loc x]
  | Pstr_exception(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_exception")) [quote_extension_constructor _loc x]
  | Pstr_module(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_module")) [quote_module_binding _loc x]
  | Pstr_recmodule(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_recmodule")) [(quote_list quote_module_binding) _loc x]
  | Pstr_modtype(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_modtype")) [quote_module_type_declaration _loc x]
  | Pstr_open(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_open")) [quote_open_description _loc x]
  | Pstr_class(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_class")) [(quote_list quote_class_declaration) _loc x]
  | Pstr_class_type(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_class_type")) [(quote_list quote_class_type_declaration) _loc x]
  | Pstr_include(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_include")) [quote_include_declaration _loc x]
  | Pstr_attribute(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_attribute")) [quote_attribute _loc x]
  | Pstr_extension(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Pstr_extension")) [ quote_extension _loc x1; quote_attributes _loc x2;]

and quote_value_binding _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pvb_pat")), quote_pattern _loc r.pvb_pat) ;
   ((Ldot(Lident "Parsetree", "pvb_expr")), quote_expression _loc r.pvb_expr) ;
   ((Ldot(Lident "Parsetree", "pvb_attributes")), quote_attributes _loc r.pvb_attributes) ;
   ((Ldot(Lident "Parsetree", "pvb_loc")), quote_location_t _loc r.pvb_loc) ;
  ]

and quote_module_binding _loc r =   quote_record _loc [
   ((Ldot(Lident "Parsetree", "pmb_name")), (quote_loc quote_string) _loc r.pmb_name) ;
   ((Ldot(Lident "Parsetree", "pmb_expr")), quote_module_expr _loc r.pmb_expr) ;
   ((Ldot(Lident "Parsetree", "pmb_attributes")), quote_attributes _loc r.pmb_attributes) ;
   ((Ldot(Lident "Parsetree", "pmb_loc")), quote_location_t _loc r.pmb_loc) ;
  ]

let rec quote_toplevel_phrase _loc x = match x with
  | Ptop_def(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptop_def")) [quote_structure _loc x]
  | Ptop_dir(x1,x2) -> quote_const _loc (Ldot(Lident "Parsetree", "Ptop_dir")) [ quote_string _loc x1; quote_directive_argument _loc x2;]

and quote_directive_argument _loc x = match x with
  | Pdir_none -> quote_const _loc (Ldot(Lident "Parsetree", "Pdir_none")) []
  | Pdir_string(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pdir_string")) [quote_string _loc x]
  | Pdir_int(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pdir_int")) [quote_int _loc x]
  | Pdir_ident(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pdir_ident")) [quote_longident _loc x]
  | Pdir_bool(x) -> quote_const _loc (Ldot(Lident "Parsetree", "Pdir_bool")) [quote_bool _loc x]

