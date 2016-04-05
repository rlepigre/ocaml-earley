open Decap
open Generate_calc

type calc_prio = Sum | Prod | Pow | Atom

let float_re = ''[0-9]+\([.][0-9]+\)?\([eE][-+]?[0-9]+\)?''
let float_num = parser
  f:RE(float_re) -> float_of_string f

let prod_sym = parser
  | '*' -> ( *. )
  | '/' -> ( /. )

let sum_sym = parser
  | '+' -> ( +. )
  | '-' -> ( -. )

let parser expr =
  | f:float_num -> (Atom,f)
  | '(' (_,e):expr ')'  -> (Atom,e)
  | '-' e:(expr_lvl Pow) -> (Pow, -. e)
  | '+' e:(expr_lvl Pow) -> (Pow, e)
  | (conditional_sequence expr
       (fun (p,e) -> if p <= Pow then give_up ""; e)
       (parser _:"**" (expr_lvl Pow)) (fun e e' -> (Pow, e ** e')))
  | (conditional_sequence expr
       (fun (p,e) -> if p < Prod then give_up ""; e)
       (parser prod_sym (expr_lvl Pow)) (fun e (fn, e') -> (Prod, fn e e')))
  | (conditional_sequence expr
       (fun (p,e) -> if p < Sum then give_up ""; e)
       (parser sum_sym (expr_lvl Prod)) (fun e (fn, e') -> (Sum, fn e e')))

and expr_lvl p =
    | (p',e):expr -> if p' < p then give_up ""; e


(* The main loop *)
let _ = run (apply snd expr)
