open Asttypes
open Parsetree
open Longident
open Pa_ast

let loc_ptyp = loc_typ
let loc_ppat = loc_pat
let loc_pexp = loc_expr
let loc_pcty = pcty_loc
let loc_pctf = pctf_loc
let loc_pmty = mtyp_loc
let loc_pmod = mexpr_loc
let loc_psig = loc_sig
let loc_pstr = loc_str

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
#ifversion <= 4.01
  | Quote_pfield (* for 4.01.0 *)
#endif

let dummy_pexp   = (exp_ident Location.none "$Antiquotation$").pexp_desc
let dummy_ppat   = (pat_ident Location.none "$Antiquotation$").ppat_desc
let dummy_ptyp   = Obj.magic (Some None)
let dummy_pcty   = Obj.magic (Some None)
let dummy_pctf   = Obj.magic (Some None)
let dummy_pcl    = Obj.magic (Some None)
let dummy_pcf    = Obj.magic (Some None)
let dummy_pmty   = Obj.magic (Some None)
let dummy_pmod   = Obj.magic (Some None)
let dummy_loc d  = d
#if version <= 4.01
let dummy_psig   = Psig_open ( Fresh, id_loc (Lident "$Antiquotation$")  Location.none)
let dummy_pstr   = Pstr_open ( Fresh, id_loc (Lident "$Antiquotation$")  Location.none)
let dummy_pfield = Obj.magic (Some None) (* for 4.01.0 *)
#else
let dummy_psig   = Psig_open { popen_lid = id_loc (Lident "$Antiquotation$")  Location.none;
			       popen_override = Fresh;
			       popen_loc = Location.none;
			       popen_attributes = [] }
let dummy_pstr   = Pstr_open { popen_lid = id_loc (Lident "$Antiquotation$")  Location.none;
			       popen_override = Fresh;
			       popen_loc = Location.none;
			       popen_attributes = [] }
#endif

let make_antiquotation loc =
  let open Lexing in
  let open Location in
  let f pos = { pos with pos_fname = "$"^pos.pos_fname^"$" } in
  { loc with loc_start = f loc.loc_start; loc_end = f loc.loc_end }

let is_antiquotation loc =
  let open Lexing in
  let open Location in
  let s = loc.loc_start.pos_fname in
  String.length s > 0 && s.[0] = '$'

let anti_table = (Hashtbl.create 101 : (Location.t, quotation -> expression) Hashtbl.t)
let string_anti_table = (Hashtbl.create 101 : (string,expression) Hashtbl.t)

(* Generic functions *)
let quote_bool : Location.t -> bool -> expression =
  Pa_ast.exp_bool

let quote_int : Location.t -> int -> expression =
  Pa_ast.exp_int

let quote_int32 : Location.t -> int32 -> expression =
  Pa_ast.exp_int32

let quote_int64 : Location.t -> int64 -> expression =
  Pa_ast.exp_int64

let quote_nativeint : Location.t -> nativeint -> expression =
  Pa_ast.exp_nativeint

let quote_char : Location.t -> char -> expression =
  Pa_ast.exp_char

let anti_string_prefix = "string antiquotation\000"
let quote_string : Location.t -> string -> expression = fun loc s ->
  try Hashtbl.find string_anti_table s
  with Not_found -> Pa_ast.exp_string loc s
let string_antiquotation _loc e =
  let key = anti_string_prefix ^ Marshal.to_string _loc [] in
  Hashtbl.add string_anti_table key e;
  key

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

let quote_apply : Location.t -> Longident.t -> expression list -> expression =
  (fun _loc s l ->
    match l with [] -> Pa_ast.exp_lident _loc s
               | [x] -> Pa_ast.exp_apply1 _loc (Pa_ast.exp_lident _loc s) x
	       | l -> Pa_ast.exp_apply _loc (Pa_ast.exp_lident _loc s) l)

let quote_const : Location.t -> Longident.t -> expression list -> expression =
  (fun _loc s l ->
    match l with [] -> Pa_ast.exp_const _loc s None
                | [x] -> Pa_ast.exp_const _loc s (Some x)
                | l -> Pa_ast.exp_const _loc s (Some (Pa_ast.exp_tuple _loc l)))

let lexing s = Ldot(Lident "Lexing", s)
let location s = Ldot(Lident "Location", s)
let longident s = Ldot(Lident "Longident", s)
let parsetree s = Ldot(Lident "Parsetree", s)
let asttypes s = Ldot(Lident "Asttypes", s)
let pa_ast s = Ldot(Lident "Pa_ast", s)

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
