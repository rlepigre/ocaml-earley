open Asttypes
open Parsetree
open Longident

let loc_id   loc x = Location.mkloc x loc
let loc_ptyp loc x = Helper.Typ.mk ~loc x
let loc_ppat loc x = Helper.Pat.mk ~loc x
let loc_pexp loc x = Helper.Exp.mk ~loc x
let loc_pcty loc x = Helper.Cty.mk ~loc x
let loc_pctf loc x = Helper.Ctf.mk ~loc x
let loc_pmty loc x = Helper.Mty.mk ~loc x
let loc_pmod loc x = Helper.Mod.mk ~loc x
let loc_psig loc x = Helper.Sig.mk ~loc x
let loc_pstr loc x = Helper.Str.mk ~loc x
let loc_pcl  loc x = Helper.Cl.mk  ~loc x
let loc_pcf  loc x = Helper.Cf.mk  ~loc x

type quotation =
  | Quote_pexp
  | Quote_ppat
  | Quote_ptyp
  | Quote_pcty
  | Quote_pctf
  | Quote_pcl
  | Quote_pcf
  | Quote_pmty
  | Quote_psig
  | Quote_pmod
  | Quote_pstr
  | Quote_loc
  | Quote_cases

let dummy_pexp =
  let lid = Location.(mkloc (Lident "$Antiquotation$") none) in
  (Helper.Exp.ident lid).pexp_desc

let dummy_ppat =
  (Helper.Pat.var Location.(mkloc "$Antiquotation$" none)).ppat_desc

let dummy_ptyp   = Obj.magic (Some None)
let dummy_pcty   = Obj.magic (Some None)
let dummy_pctf   = Obj.magic (Some None)
let dummy_pcl    = Obj.magic (Some None)
let dummy_pcf    = Obj.magic (Some None)
let dummy_pmty   = Obj.magic (Some None)
let dummy_pmod   = Obj.magic (Some None)
let dummy_loc d  = d
let dummy_psig   =
  Psig_open
    { popen_lid        = Location.(mkloc (Lident "$Antiquotation$") none)
    ; popen_override   = Fresh
    ; popen_loc        = Location.none
    ; popen_attributes = [] }
let dummy_pstr   =
  Pstr_open
    { popen_lid        = Location.(mkloc (Lident "$Antiquotation$") none)
    ; popen_override   = Fresh
    ; popen_loc        = Location.none
    ; popen_attributes = [] }

let anti_table : (Location.t, quotation -> expression) Hashtbl.t =
  Hashtbl.create 101

let string_anti_table : (string, expression) Hashtbl.t =
  Hashtbl.create 101

let make_antiquotation loc =
  let open Lexing in
  let open Location in
  let f pos = { pos with pos_fname = "$"^pos.pos_fname^"$" } in
  { loc with loc_start = f loc.loc_start; loc_end = f loc.loc_end }

let make_list_antiquotation loc qtyp f =
  let loc = make_antiquotation loc in
  Hashtbl.add anti_table loc f;
  let rec l = Obj.magic loc :: Obj.magic qtyp :: l in
  l

let is_antiquotation loc =
  let open Lexing in
  let open Location in
  let s = loc.loc_start.pos_fname in
  String.length s > 0 && s.[0] = '$'

let is_list_antiquotation l =
  match l with
  | loc::qtyp::l' when l == l' ->
     let loc : Location.t = Obj.magic loc in
     if is_antiquotation loc then Some(loc, (Obj.magic qtyp : quotation))
     else None
  | _ -> None

let lexing    s = Ldot(Lident "Lexing"   , s)
let location  s = Ldot(Lident "Location" , s)
let longident s = Ldot(Lident "Longident", s)
let parsetree s = Ldot(Lident "Parsetree", s)
let asttypes  s = Ldot(Lident "Asttypes" , s)

type 'a quote = expression -> Location.t -> 'a -> expression

(* Generic functions *)
let quote_int : int quote = fun _ loc i ->
  Helper.Exp.constant ~loc (Helper.Const.int i)

let quote_int32 : int32 quote = fun _ loc i ->
  Helper.Exp.constant ~loc (Helper.Const.int32 ~suffix:'l' i)

let quote_int64 : int64 quote = fun _ loc i ->
  Helper.Exp.constant ~loc (Helper.Const.int64 ~suffix:'L' i)

let quote_nativeint : nativeint quote = fun _ loc i ->
  Helper.Exp.constant ~loc (Helper.Const.nativeint ~suffix:'n' i)

let quote_char : char quote = fun _ loc c ->
  Helper.Exp.constant ~loc (Helper.Const.char c)

let quote_string : string quote = fun _ loc s ->
  try Hashtbl.find string_anti_table s
  with Not_found -> Helper.Exp.constant ~loc (Helper.Const.string s)

let quote_bool : bool quote = fun _ loc b ->
  let b = if b then "true" else "false" in
  Helper.Exp.construct ~loc (Location.mkloc (Lident b) loc) None

let string_antiquotation loc e =
  let key = "string antiquotation\000" ^ Marshal.to_string loc [] in
  Hashtbl.add string_anti_table key e; key

let quote_list : 'a quote -> 'a list quote = fun qe e_loc _loc el ->
  let exp_list loc es =
    let open Helper in
    let nil = Exp.construct ~loc (Location.mkloc (Lident "[]") loc) None in
    let cns hd tl =
      let arg = Exp.tuple ~loc [hd; tl] in
      Exp.construct ~loc (Location.mkloc (Lident "::") loc) (Some arg)
    in
    List.fold_right cns es nil
  in
  match is_list_antiquotation el with
  | None         -> exp_list _loc (List.map (qe e_loc _loc) el)
  | Some(loc,qt) -> try Hashtbl.find anti_table loc qt with Not_found ->
                      failwith "antiquotation not in a quotation"

let quote_tuple : expression list quote = fun _ loc l ->
  Helper.Exp.tuple ~loc l

let quote_record : (Longident.t * expression) list quote = fun _ loc l ->
  let fn (id, e) = (Location.mkloc id loc, e) in
  Helper.Exp.record ~loc (List.map fn l) None

let quote_apply : (Longident.t * expression list) quote = fun _ loc (s, l) ->
  let e = Helper.Exp.ident ~loc (Location.mkloc s loc) in
  match l with
  | [] -> e
  | _  -> Helper.Exp.apply ~loc e (List.map (fun e -> (Nolabel, e)) l)

let quote_const : (Longident.t * expression list) quote = fun _ loc (s, l) ->
  let arg =
    match l with
    | []  -> None
    | [x] -> Some x
    | l   -> Some (Helper.Exp.tuple ~loc l)
  in
  Helper.Exp.construct ~loc (Location.mkloc s loc) arg

let quote_option : 'a quote -> 'a option quote = fun qe e_loc loc eo ->
  match eo with
  | None   -> let none = Location.mkloc (Lident "None") loc in
              Helper.Exp.construct ~loc none None
  | Some e -> let some = Location.mkloc (Lident "Some") loc in
              Helper.Exp.construct ~loc some (Some (qe e_loc loc e))

let rec quote_longident : Longident.t quote = fun e_loc loc l ->
  match l with
  | Lident(s)     -> let s = quote_string e_loc loc s in
                     quote_const e_loc loc (longident "Lident", [s])
  | Ldot(l,s)     -> let l = quote_longident e_loc loc l in
                     let s = quote_string e_loc loc s in
                     quote_const e_loc loc (longident "Ldot", [l; s])
  | Lapply(l1,l2) -> let l1 = quote_longident e_loc loc l1 in
                     let l2 = quote_longident e_loc loc l2 in
                     quote_const e_loc loc (longident "Lapply", [l1; l2])

let quote_position : Lexing.position quote = fun e_loc loc pos ->
  quote_record e_loc loc
    [ (lexing "pos_fname", quote_string e_loc loc pos.Lexing.pos_fname)
    ; (lexing "pos_lnum" , quote_int    e_loc loc pos.Lexing.pos_lnum )
    ; (lexing "pos_bol"  , quote_int    e_loc loc pos.Lexing.pos_bol  )
    ; (lexing "pos_cnum" , quote_int    e_loc loc pos.Lexing.pos_cnum ) ]

(* Forget the original location of the quotation. *)
let quote_parser_position = ref false

let quote_location_t : Location.t quote = fun e_loc loc l ->
  if !quote_parser_position then
    quote_record e_loc loc
      [ (location "loc_start", quote_position e_loc loc l.Location.loc_start)
      ; (location "loc_end"  , quote_position e_loc loc l.Location.loc_end  )
      ; (location "loc_ghost", quote_bool     e_loc loc l.Location.loc_ghost)]
  else e_loc
