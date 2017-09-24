open Generate_calc
open Earley

type calc_prio = Sum | Pro | Pow | Atm

let prio_to_string = function
  | Sum  -> "Sum"
  | Pro -> "Prod"
  | Pow -> "Pow"
  | Atm -> "Atom"

let float_re = ''[0-9]+\([.][0-9]+\)?\([eE][-+]?[0-9]+\)?''
let float_num = parser
  f:RE(float_re) -> float_of_string f

let pro_sym = parser
  | '*' -> ( *. )
  | '/' -> ( /. )

let sum_sym = parser
  | '+' -> ( +. )
  | '-' -> ( -. )

let (expr, set_expr) = grammar_prio ~param_to_string:prio_to_string "expr"

let _ = set_expr
  [ ((fun p -> true    ), parser float_num )
  ; ((fun p -> true    ), parser '(' e:(expr Sum) ')')
  ; ((fun p -> p <= Pow), parser '-' e:(expr Pow)                 -> -. e)
  ; ((fun p -> p <= Pow), parser '+' e:(expr Pow))
  ; ((fun p -> p <= Pow), parser e:(expr Atm) "**" e':(expr Pow) -> e ** e')
  ; ((fun p -> p <= Pro), parser e:(expr Pro) fn:pro_sym e':(expr Pow) -> fn e e')
  ; ((fun p -> p <= Sum), parser e:(expr Sum) fn:sum_sym e':(expr Pro) -> fn e e')
  ]

(* The main loop *)
let _ = run (expr Sum)
