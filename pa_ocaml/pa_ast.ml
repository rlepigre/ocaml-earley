open Asttypes
open Parsetree
open Longident

let exp_string loc s    = Helper.Exp.constant ~loc (Helper.Const.string s)
let exp_char loc c      = Helper.Exp.constant ~loc (Helper.Const.char c)
let exp_float loc f     = Helper.Exp.constant ~loc (Helper.Const.float f)
let exp_int loc i       = Helper.Exp.constant ~loc (Helper.Const.int i)
let exp_int32 loc i     = Helper.Exp.constant ~loc (Helper.Const.int32 ~suffix:'l' i)
let exp_int64 loc i     = Helper.Exp.constant ~loc (Helper.Const.int64 ~suffix:'L' i)
let exp_nativeint loc i = Helper.Exp.constant ~loc (Helper.Const.nativeint ~suffix:'n' i)

let exp_tuple loc l =
  match l with
  | []  -> Helper.Exp.construct ~loc (Location.mkloc (Lident "()") loc) None
  | [e] -> e
  | _   -> Helper.Exp.tuple ~loc l

let exp_array loc l = Helper.Exp.array ~loc l
let exp_lident loc id = Helper.Exp.ident ~loc (Location.mkloc id loc)
let exp_ident loc id = exp_lident loc (Lident id)
let pat_ident loc id = Helper.Pat.var ~loc (Location.mkloc id loc)
let pat_array loc l = Helper.Pat.array ~loc l

let typ_tuple loc l =
  match l with
  | []  -> Helper.Typ.constr ~loc (Location.mkloc (Lident "unit") loc) []
  | [t] -> t
  | _   -> Helper.Typ.tuple ~loc l

let pat_tuple loc l =
  match l with
  | []  -> Helper.Pat.construct ~loc (Location.mkloc (Lident "()") loc) None
  | [p] -> p
  | _   -> Helper.Pat.tuple ~loc l
