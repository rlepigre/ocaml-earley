open Asttypes
open Parsetree
open Longident
let iter_option fn o1 = match o1 with | None  -> () | Some e1 -> fn e1
let iter_list = List.iter
let do_local_ident = ref (fun _  -> ())
let rec iter_longident i1 =
  match i1 with | Lident s1 -> (!do_local_ident) s1 | _ -> ()
(* asttypes.mli *)
let iter_constant c1 =
  match c1 with
  | Const_int(x) -> (fun _ -> ()) x
  | Const_char(x) -> (fun _ -> ()) x
  | Const_string(x) -> (fun _ -> ()) x
  | Const_float(x) -> (fun _ -> ()) x
  | Const_int32(x) -> (fun _ -> ()) x
  | Const_int64(x) -> (fun _ -> ()) x
  | Const_nativeint(x) -> (fun _ -> ()) x

let iter_rec_flag c1 =
  match c1 with
  | Nonrecursive -> ()
  | Recursive -> ()
  | Default -> ()

let iter_direction_flag c1 =
  match c1 with
  | Upto -> ()
  | Downto -> ()

let iter_private_flag c1 =
  match c1 with
  | Private -> ()
  | Public -> ()

let iter_mutable_flag c1 =
  match c1 with
  | Immutable -> ()
  | Mutable -> ()

let iter_virtual_flag c1 =
  match c1 with
  | Virtual -> ()
  | Concrete -> ()

let iter_override_flag c1 =
  match c1 with
  | Override -> ()
  | Fresh -> ()

let iter_closed_flag c1 =
  match c1 with
  | Closed -> ()
  | Open -> ()

let iter_label c1 = (fun _ -> ()) c1
let iter_loc : 'a. ('a -> unit) -> 'a loc -> unit = fun iter_a r1 -> () ; iter_a r1.txt  ; (fun _ -> ()) r1.loc 

(* parsetree.mli *)
let rec iter_core_type = fun r1 -> () ; iter_core_type_desc r1.ptyp_desc  ; (fun _ -> ()) r1.ptyp_loc 
and iter_core_type_desc c1 =
  match c1 with
  | Ptyp_any -> ()
  | Ptyp_var(x) -> (fun _ -> ()) x
  | Ptyp_arrow(x1,x2,x3) -> () ; (iter_label x1) ; (iter_core_type x2) ; (iter_core_type x3)  | Ptyp_tuple(x) -> (iter_list iter_core_type) x
  | Ptyp_constr(x1,x2) -> () ; ((iter_loc iter_longident) x1) ; ((iter_list iter_core_type) x2)  | Ptyp_object(x) -> (iter_list iter_core_field_type) x
  | Ptyp_class(x1,x2,x3) -> () ; ((iter_loc iter_longident) x1) ; ((iter_list iter_core_type) x2) ; ((iter_list iter_label) x3)  | Ptyp_alias(x1,x2) -> () ; (iter_core_type x1) ; ((fun _ -> ()) x2)  | Ptyp_variant(x1,x2,x3) -> () ; ((iter_list iter_row_field) x1) ; ((fun _ -> ()) x2) ; ((iter_option (iter_list iter_label)) x3)  | Ptyp_poly(x1,x2) -> () ; ((iter_list (fun _ -> ())) x1) ; (iter_core_type x2)  | Ptyp_package(x) -> iter_package_type x

and iter_package_type c1 = (fun (x1,x2) -> () ; ((iter_loc iter_longident) x1) ; ((iter_list (fun (x1,x2) -> () ; ((iter_loc iter_longident) x1) ; (iter_core_type x2))) x2)) c1
and iter_core_field_type = fun r1 -> () ; iter_core_field_desc r1.pfield_desc  ; (fun _ -> ()) r1.pfield_loc 
and iter_core_field_desc c1 =
  match c1 with
  | Pfield(x1,x2) -> () ; ((fun _ -> ()) x1) ; (iter_core_type x2)  | Pfield_var -> ()

and iter_row_field c1 =
  match c1 with
  | Rtag(x1,x2,x3) -> () ; (iter_label x1) ; ((fun _ -> ()) x2) ; ((iter_list iter_core_type) x3)  | Rinherit(x) -> iter_core_type x

let iter_class_infos : 'a. ('a -> unit) -> 'a class_infos -> unit = fun iter_a r1 -> () ; iter_virtual_flag r1.pci_virt  ; (fun (x1,x2) -> () ; ((iter_list (iter_loc (fun _ -> ()))) x1) ; ((fun _ -> ()) x2)) r1.pci_params  ; (iter_loc (fun _ -> ())) r1.pci_name  ; iter_a r1.pci_expr  ; (iter_list (fun (x1,x2) -> () ; ((fun _ -> ()) x1) ; ((fun _ -> ()) x2))) r1.pci_variance  ; (fun _ -> ()) r1.pci_loc 
let rec iter_pattern = fun r1 -> () ; iter_pattern_desc r1.ppat_desc  ; (fun _ -> ()) r1.ppat_loc 
and iter_pattern_desc c1 =
  match c1 with
  | Ppat_any -> ()
  | Ppat_var(x) -> (iter_loc (fun _ -> ())) x
  | Ppat_alias(x1,x2) -> () ; (iter_pattern x1) ; ((iter_loc (fun _ -> ())) x2)  | Ppat_constant(x) -> iter_constant x
  | Ppat_tuple(x) -> (iter_list iter_pattern) x
  | Ppat_construct(x1,x2,x3) -> () ; ((iter_loc iter_longident) x1) ; ((iter_option iter_pattern) x2) ; ((fun _ -> ()) x3)  | Ppat_variant(x1,x2) -> () ; (iter_label x1) ; ((iter_option iter_pattern) x2)  | Ppat_record(x1,x2) -> () ; ((iter_list (fun (x1,x2) -> () ; ((iter_loc iter_longident) x1) ; (iter_pattern x2))) x1) ; (iter_closed_flag x2)  | Ppat_array(x) -> (iter_list iter_pattern) x
  | Ppat_or(x1,x2) -> () ; (iter_pattern x1) ; (iter_pattern x2)  | Ppat_constraint(x1,x2) -> () ; (iter_pattern x1) ; (iter_core_type x2)  | Ppat_type(x) -> (iter_loc iter_longident) x
  | Ppat_lazy(x) -> iter_pattern x
  | Ppat_unpack(x) -> (iter_loc (fun _ -> ())) x

let rec iter_expression = fun r1 -> () ; iter_expression_desc r1.pexp_desc  ; (fun _ -> ()) r1.pexp_loc 
and iter_expression_desc c1 =
  match c1 with
  | Pexp_ident(x) -> (iter_loc iter_longident) x
  | Pexp_constant(x) -> iter_constant x
  | Pexp_let(x1,x2,x3) -> () ; (iter_rec_flag x1) ; ((iter_list (fun (x1,x2) -> () ; (iter_pattern x1) ; (iter_expression x2))) x2) ; (iter_expression x3)  | Pexp_function(x1,x2,x3) -> () ; (iter_label x1) ; ((iter_option iter_expression) x2) ; ((iter_list (fun (x1,x2) -> () ; (iter_pattern x1) ; (iter_expression x2))) x3)  | Pexp_apply(x1,x2) -> () ; (iter_expression x1) ; ((iter_list (fun (x1,x2) -> () ; (iter_label x1) ; (iter_expression x2))) x2)  | Pexp_match(x1,x2) -> () ; (iter_expression x1) ; ((iter_list (fun (x1,x2) -> () ; (iter_pattern x1) ; (iter_expression x2))) x2)  | Pexp_try(x1,x2) -> () ; (iter_expression x1) ; ((iter_list (fun (x1,x2) -> () ; (iter_pattern x1) ; (iter_expression x2))) x2)  | Pexp_tuple(x) -> (iter_list iter_expression) x
  | Pexp_construct(x1,x2,x3) -> () ; ((iter_loc iter_longident) x1) ; ((iter_option iter_expression) x2) ; ((fun _ -> ()) x3)  | Pexp_variant(x1,x2) -> () ; (iter_label x1) ; ((iter_option iter_expression) x2)  | Pexp_record(x1,x2) -> () ; ((iter_list (fun (x1,x2) -> () ; ((iter_loc iter_longident) x1) ; (iter_expression x2))) x1) ; ((iter_option iter_expression) x2)  | Pexp_field(x1,x2) -> () ; (iter_expression x1) ; ((iter_loc iter_longident) x2)  | Pexp_setfield(x1,x2,x3) -> () ; (iter_expression x1) ; ((iter_loc iter_longident) x2) ; (iter_expression x3)  | Pexp_array(x) -> (iter_list iter_expression) x
  | Pexp_ifthenelse(x1,x2,x3) -> () ; (iter_expression x1) ; (iter_expression x2) ; ((iter_option iter_expression) x3)  | Pexp_sequence(x1,x2) -> () ; (iter_expression x1) ; (iter_expression x2)  | Pexp_while(x1,x2) -> () ; (iter_expression x1) ; (iter_expression x2)  | Pexp_for(x1,x2,x3,x4,x5) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_expression x2) ; (iter_expression x3) ; (iter_direction_flag x4) ; (iter_expression x5)  | Pexp_constraint(x1,x2,x3) -> () ; (iter_expression x1) ; ((iter_option iter_core_type) x2) ; ((iter_option iter_core_type) x3)  | Pexp_when(x1,x2) -> () ; (iter_expression x1) ; (iter_expression x2)  | Pexp_send(x1,x2) -> () ; (iter_expression x1) ; ((fun _ -> ()) x2)  | Pexp_new(x) -> (iter_loc iter_longident) x
  | Pexp_setinstvar(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_expression x2)  | Pexp_override(x) -> (iter_list (fun (x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_expression x2))) x
  | Pexp_letmodule(x1,x2,x3) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_expr x2) ; (iter_expression x3)  | Pexp_assert(x) -> iter_expression x
  | Pexp_assertfalse -> ()
  | Pexp_lazy(x) -> iter_expression x
  | Pexp_poly(x1,x2) -> () ; (iter_expression x1) ; ((iter_option iter_core_type) x2)  | Pexp_object(x) -> iter_class_structure x
  | Pexp_newtype(x1,x2) -> () ; ((fun _ -> ()) x1) ; (iter_expression x2)  | Pexp_pack(x) -> iter_module_expr x
  | Pexp_open(x1,x2,x3) -> () ; (iter_override_flag x1) ; ((iter_loc iter_longident) x2) ; (iter_expression x3)
and iter_value_description = fun r1 -> () ; iter_core_type r1.pval_type  ; (iter_list (fun _ -> ())) r1.pval_prim  ; (fun _ -> ()) r1.pval_loc 
and iter_type_declaration = fun r1 -> () ; (iter_list (iter_option (iter_loc (fun _ -> ())))) r1.ptype_params  ; (iter_list (fun (x1,x2,x3) -> () ; (iter_core_type x1) ; (iter_core_type x2) ; ((fun _ -> ()) x3))) r1.ptype_cstrs  ; iter_type_kind r1.ptype_kind  ; iter_private_flag r1.ptype_private  ; (iter_option iter_core_type) r1.ptype_manifest  ; (iter_list (fun (x1,x2) -> () ; ((fun _ -> ()) x1) ; ((fun _ -> ()) x2))) r1.ptype_variance  ; (fun _ -> ()) r1.ptype_loc 
and iter_type_kind c1 =
  match c1 with
  | Ptype_abstract -> ()
  | Ptype_variant(x) -> (iter_list (fun (x1,x2,x3,x4) -> () ; ((iter_loc (fun _ -> ())) x1) ; ((iter_list iter_core_type) x2) ; ((iter_option iter_core_type) x3) ; ((fun _ -> ()) x4))) x
  | Ptype_record(x) -> (iter_list (fun (x1,x2,x3,x4) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_mutable_flag x2) ; (iter_core_type x3) ; ((fun _ -> ()) x4))) x

and iter_exception_declaration c1 = (iter_list iter_core_type) c1
and iter_class_type = fun r1 -> () ; iter_class_type_desc r1.pcty_desc  ; (fun _ -> ()) r1.pcty_loc 
and iter_class_type_desc c1 =
  match c1 with
  | Pcty_constr(x1,x2) -> () ; ((iter_loc iter_longident) x1) ; ((iter_list iter_core_type) x2)  | Pcty_signature(x) -> iter_class_signature x
  | Pcty_fun(x1,x2,x3) -> () ; (iter_label x1) ; (iter_core_type x2) ; (iter_class_type x3)
and iter_class_signature = fun r1 -> () ; iter_core_type r1.pcsig_self  ; (iter_list iter_class_type_field) r1.pcsig_fields  ; (fun _ -> ()) r1.pcsig_loc 
and iter_class_type_field = fun r1 -> () ; iter_class_type_field_desc r1.pctf_desc  ; (fun _ -> ()) r1.pctf_loc 
and iter_class_type_field_desc c1 =
  match c1 with
  | Pctf_inher(x) -> iter_class_type x
  | Pctf_val(x1,x2,x3,x4) -> () ; ((fun _ -> ()) x1) ; (iter_mutable_flag x2) ; (iter_virtual_flag x3) ; (iter_core_type x4)  | Pctf_virt(x1,x2,x3) -> () ; ((fun _ -> ()) x1) ; (iter_private_flag x2) ; (iter_core_type x3)  | Pctf_meth(x1,x2,x3) -> () ; ((fun _ -> ()) x1) ; (iter_private_flag x2) ; (iter_core_type x3)  | Pctf_cstr(x1,x2) -> () ; (iter_core_type x1) ; (iter_core_type x2)
and iter_class_description c1 = (iter_class_infos iter_class_type) c1
and iter_class_type_declaration c1 = (iter_class_infos iter_class_type) c1
and iter_class_expr = fun r1 -> () ; iter_class_expr_desc r1.pcl_desc  ; (fun _ -> ()) r1.pcl_loc 
and iter_class_expr_desc c1 =
  match c1 with
  | Pcl_constr(x1,x2) -> () ; ((iter_loc iter_longident) x1) ; ((iter_list iter_core_type) x2)  | Pcl_structure(x) -> iter_class_structure x
  | Pcl_fun(x1,x2,x3,x4) -> () ; (iter_label x1) ; ((iter_option iter_expression) x2) ; (iter_pattern x3) ; (iter_class_expr x4)  | Pcl_apply(x1,x2) -> () ; (iter_class_expr x1) ; ((iter_list (fun (x1,x2) -> () ; (iter_label x1) ; (iter_expression x2))) x2)  | Pcl_let(x1,x2,x3) -> () ; (iter_rec_flag x1) ; ((iter_list (fun (x1,x2) -> () ; (iter_pattern x1) ; (iter_expression x2))) x2) ; (iter_class_expr x3)  | Pcl_constraint(x1,x2) -> () ; (iter_class_expr x1) ; (iter_class_type x2)
and iter_class_structure = fun r1 -> () ; iter_pattern r1.pcstr_pat  ; (iter_list iter_class_field) r1.pcstr_fields 
and iter_class_field = fun r1 -> () ; iter_class_field_desc r1.pcf_desc  ; (fun _ -> ()) r1.pcf_loc 
and iter_class_field_desc c1 =
  match c1 with
  | Pcf_inher(x1,x2,x3) -> () ; (iter_override_flag x1) ; (iter_class_expr x2) ; ((iter_option (fun _ -> ())) x3)  | Pcf_valvirt(x1,x2,x3) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_mutable_flag x2) ; (iter_core_type x3)  | Pcf_val(x1,x2,x3,x4) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_mutable_flag x2) ; (iter_override_flag x3) ; (iter_expression x4)  | Pcf_virt(x1,x2,x3) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_private_flag x2) ; (iter_core_type x3)  | Pcf_meth(x1,x2,x3,x4) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_private_flag x2) ; (iter_override_flag x3) ; (iter_expression x4)  | Pcf_constr(x1,x2) -> () ; (iter_core_type x1) ; (iter_core_type x2)  | Pcf_init(x) -> iter_expression x

and iter_class_declaration c1 = (iter_class_infos iter_class_expr) c1
and iter_module_type = fun r1 -> () ; iter_module_type_desc r1.pmty_desc  ; (fun _ -> ()) r1.pmty_loc 
and iter_module_type_desc c1 =
  match c1 with
  | Pmty_ident(x) -> (iter_loc iter_longident) x
  | Pmty_signature(x) -> iter_signature x
  | Pmty_functor(x1,x2,x3) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_type x2) ; (iter_module_type x3)  | Pmty_with(x1,x2) -> () ; (iter_module_type x1) ; ((iter_list (fun (x1,x2) -> () ; ((iter_loc iter_longident) x1) ; (iter_with_constraint x2))) x2)  | Pmty_typeof(x) -> iter_module_expr x

and iter_signature c1 = (iter_list iter_signature_item) c1
and iter_signature_item = fun r1 -> () ; iter_signature_item_desc r1.psig_desc  ; (fun _ -> ()) r1.psig_loc 
and iter_signature_item_desc c1 =
  match c1 with
  | Psig_value(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_value_description x2)  | Psig_type(x) -> (iter_list (fun (x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_type_declaration x2))) x
  | Psig_exception(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_exception_declaration x2)  | Psig_module(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_type x2)  | Psig_recmodule(x) -> (iter_list (fun (x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_type x2))) x
  | Psig_modtype(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_modtype_declaration x2)  | Psig_open(x1,x2) -> () ; (iter_override_flag x1) ; ((iter_loc iter_longident) x2)  | Psig_include(x) -> iter_module_type x
  | Psig_class(x) -> (iter_list iter_class_description) x
  | Psig_class_type(x) -> (iter_list iter_class_type_declaration) x

and iter_modtype_declaration c1 =
  match c1 with
  | Pmodtype_abstract -> ()
  | Pmodtype_manifest(x) -> iter_module_type x

and iter_with_constraint c1 =
  match c1 with
  | Pwith_type(x) -> iter_type_declaration x
  | Pwith_module(x) -> (iter_loc iter_longident) x
  | Pwith_typesubst(x) -> iter_type_declaration x
  | Pwith_modsubst(x) -> (iter_loc iter_longident) x

and iter_module_expr = fun r1 -> () ; iter_module_expr_desc r1.pmod_desc  ; (fun _ -> ()) r1.pmod_loc 
and iter_module_expr_desc c1 =
  match c1 with
  | Pmod_ident(x) -> (iter_loc iter_longident) x
  | Pmod_structure(x) -> iter_structure x
  | Pmod_functor(x1,x2,x3) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_type x2) ; (iter_module_expr x3)  | Pmod_apply(x1,x2) -> () ; (iter_module_expr x1) ; (iter_module_expr x2)  | Pmod_constraint(x1,x2) -> () ; (iter_module_expr x1) ; (iter_module_type x2)  | Pmod_unpack(x) -> iter_expression x

and iter_structure c1 = (iter_list iter_structure_item) c1
and iter_structure_item = fun r1 -> () ; iter_structure_item_desc r1.pstr_desc  ; (fun _ -> ()) r1.pstr_loc 
and iter_structure_item_desc c1 =
  match c1 with
  | Pstr_eval(x) -> iter_expression x
  | Pstr_value(x1,x2) -> () ; (iter_rec_flag x1) ; ((iter_list (fun (x1,x2) -> () ; (iter_pattern x1) ; (iter_expression x2))) x2)  | Pstr_primitive(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_value_description x2)  | Pstr_type(x) -> (iter_list (fun (x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_type_declaration x2))) x
  | Pstr_exception(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_exception_declaration x2)  | Pstr_exn_rebind(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; ((iter_loc iter_longident) x2)  | Pstr_module(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_expr x2)  | Pstr_recmodule(x) -> (iter_list (fun (x1,x2,x3) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_type x2) ; (iter_module_expr x3))) x
  | Pstr_modtype(x1,x2) -> () ; ((iter_loc (fun _ -> ())) x1) ; (iter_module_type x2)  | Pstr_open(x1,x2) -> () ; (iter_override_flag x1) ; ((iter_loc iter_longident) x2)  | Pstr_class(x) -> (iter_list iter_class_declaration) x
  | Pstr_class_type(x) -> (iter_list iter_class_type_declaration) x
  | Pstr_include(x) -> iter_module_expr x

let rec iter_toplevel_phrase c1 =
  match c1 with
  | Ptop_def(x) -> iter_structure x
  | Ptop_dir(x1,x2) -> () ; ((fun _ -> ()) x1) ; (iter_directive_argument x2)
and iter_directive_argument c1 =
  match c1 with
  | Pdir_none -> ()
  | Pdir_string(x) -> (fun _ -> ()) x
  | Pdir_int(x) -> (fun _ -> ()) x
  | Pdir_ident(x) -> iter_longident x
  | Pdir_bool(x) -> (fun _ -> ()) x

