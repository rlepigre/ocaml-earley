(** Location attached to antiquotation. *)
let _loc = Location.none

let test_expr_1 : Parsetree.expression -> Parsetree.expression = fun e ->
  <:expr<if true then $e$ else $e$>>

let test_expr_2 : Parsetree.expression -> Parsetree.expression = fun e ->
  <:expr<1 + $e$ + $e$>>

let test_expr_3 : Parsetree.expression -> Parsetree.expression ->
                  Parsetree.expression -> Parsetree.expression = fun x y z ->
  <:expr<3 * $x$ * (match $y$ with _ -> $y$ $z$ | _ -> $x$) + 2>>

let test_expr_bool_1 : Parsetree.expression =
  <:expr<if true then 1 else 2>>

let test_expr_bool_2 : bool -> Parsetree.expression = fun b ->
  <:expr<if $bool:true && b$ then 1 else 2>>

let test_expr_int_1 : Parsetree.expression =
  <:expr<2 + 2>>

let test_expr_int_2 : int -> Parsetree.expression = fun i ->
  <:expr<$int:i$ + 2>>

let test_expr_int_3 : int -> int -> Parsetree.expression = fun i j ->
  <:expr< $int:i$ + $int:j$ >>

let test_expr_string : string -> Parsetree.expression = fun s ->
  <:expr<"blabla" ^ $string:s$>>

let test_type : Parsetree.core_type =
  <:type<int -> bool -> (int, string) Hashtbl.t>>

let test_longident_t : Longident.t -> Parsetree.expression = fun lid ->
  <:expr<$longident:lid$ 42>>

let test_lid_1 : string -> Parsetree.expression = fun id ->
  <:expr<$lid:id$>>

let test_lid_2 : string -> Parsetree.expression = fun id ->
  <:expr<fun $lid:id^"toto"$ -> $lid:id^"toto"$>>

let test_pat_int : int -> int -> Parsetree.pattern -> Parsetree.expression ->
                   Parsetree.expression = fun i j p e ->
  <:expr<function $int:i$ -> $int:j$ | $p$ -> $e$>>

let test_struct : Parsetree.structure -> Parsetree.structure = fun str ->
  <:struct<
    let id x = x
    $struct:str$
  >>

let test_struct_uid : string -> Parsetree.structure = fun id ->
  <:struct<
    open $uid:id$
    let x = $uid:id$.x
  >>

(** FIXME cleanup from here on. *)


(*let f9 x y t p = <:expr<3 * $x$ * (match $y$ : $t$ with $p$ -> $y$ | _ -> $x$) + 2>>*)

let f10 a x y = <:struct<let $lid:a$ = $x$ and b = $lid:y$>>

(*let f11 x y = <:sig<val $lid:x$ : $y$>>*)

let f12 x y z = <:expr< ($list:x$, $array:y$, $tuple:z$) >>

let f13 x y z x' y' z' = <:expr< fun ($list:x$, $array:y$, $tuple:z$) -> ($list:x'$, $array:y'$, $tuple:z'$) >>

let blabla x y = <:type<int -> $tuple:x$>>

(*

let j a b c d e f g h = <:expr<$bool:a$, $int:b$, $int32:c$, $int64:d$, $natint:e$, $char:f$, $string:g$, $float:h$>>

let k a b c1 c2 cs1 cs2 = <:structure<type ('$ident:a$) $lid:b$ = $uid:c1$ | $uid:c2$ of '$ident:a$ | $cs1$ | $cs2$ >>

let l a b = <:type<[ `$ident:a$ | `$ident:b$ ]>>

let fc x = <:constructors< $x$ >>

let ff x = <:fields< $x$ >>

let fb x = <:bindings< $bindings:x$ >>

let fc x = <:cases< $cases:x$ >>

let fm x = <:module< $x$ >>

let ft x = <:module type< $x$ >>
*)
