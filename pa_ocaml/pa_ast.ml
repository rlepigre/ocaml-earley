open Asttypes
open Parsetree
open Longident

let loc_expr ?(attributes=[]) loc e    = {pexp_desc = e   ; pexp_loc = loc; pexp_attributes = attributes}
let loc_pat  ?(attributes=[]) loc pat  = {ppat_desc = pat ; ppat_loc = loc; ppat_attributes = attributes}
let loc_typ  ?(attributes=[]) loc typ  = {ptyp_desc = typ ; ptyp_loc = loc; ptyp_attributes = attributes}
let loc_pcf  ?(attributes=[]) loc desc = {pcf_desc  = desc; pcf_loc  = loc; pcf_attributes  = attributes}

let merge2 l1 l2 =
  let loc_start = l1.Location.loc_start and loc_end = l2.Location.loc_end in
  Location.({loc_start; loc_end; loc_ghost = l1.loc_ghost && l2.loc_ghost})

let rec merge ls =
  match ls with
  | []    -> assert false
  | [loc] -> loc
  | l1::_ -> let rec fn = function
               | []     -> assert false
               | [l]    -> l
               | l2::ls -> if Location.(l2.loc_start = l2.loc_end) then fn ls
                           else merge2 l1 l2
             in
             fn (List.rev ls)

let exp_string loc s    = Helper.Exp.constant ~loc (Helper.Const.string s)
let exp_char loc c      = Helper.Exp.constant ~loc (Helper.Const.char c)
let exp_float loc f     = Helper.Exp.constant ~loc (Helper.Const.float f)
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

let typ_tuple _loc l =
  match l with
  | []  -> loc_typ _loc (Ptyp_constr (Location.mkloc (Lident "unit") _loc, []))
  | [t] -> t
  | _   -> loc_typ _loc (Ptyp_tuple l)

let pat_tuple loc l =
  match l with
  | []  -> Helper.Pat.construct ~loc (Location.mkloc (Lident "()") loc) None
  | [p] -> p
  | _   -> Helper.Pat.tuple ~loc l
