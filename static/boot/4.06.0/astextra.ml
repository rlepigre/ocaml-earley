(** Extra types missing for old version *)

open Asttypes
open Docstrings
open Parsetree

type 'a open_infos =
    {
     popen_expr: 'a;
     popen_override: override_flag;
     popen_loc: Location.t;
     popen_attributes: attributes;
    }

type open_declaration = module_expr open_infos

type binding_op =
  {
    pbop_op : string loc;
    pbop_pat : pattern;
    pbop_exp : expression;
    pbop_loc : Location.t;
  }

type type_exception =
  {
    ptyexn_constructor: extension_constructor;
    ptyexn_loc: Location.t;
    ptyexn_attributes: attributes; (* ... [@@id1] [@@id2] *)
  }

type module_substitution =
  {
    pms_name: string loc;
    pms_manifest: Longident.t loc;
    pms_attributes: attributes; (* ... [@@id1] [@@id2] *)
    pms_loc: Location.t;
  }

type row_field_desc = row_field

type object_field_desc = object_field

type lid = Longident.t loc
type str = string loc
type loc = Location.t
type attrs = attribute list
