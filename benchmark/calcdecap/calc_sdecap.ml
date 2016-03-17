open Decap

type calc_prio = Sum | Prod | Pow | Atom
let expr, set_expr = grammar_family "expr" 

#define GREEDY 1

let float_num =
  let float_re = ''[0-9]+\([.][0-9]+\)?\([eE][-+]?[0-9]+\)?'' in
  parser
  | f:RE(float_re) -> float_of_string f

let prod_sym =
  parser
  | '*' -> ( *. )
  | '/' -> ( /. )

let sum_sym =
  parser
  | '+' -> ( +. )
  | '-' -> ( -. )

let _ = set_expr (fun prio ->
  parser
  | f:float_num          when prio = Atom -> f
  | '(' e:(expr Sum) ')' when prio = Atom -> e
  | '-' e:(expr Pow)    when prio = Pow -> -. e
  | '+' e:(expr Pow)    when prio = Pow -> e
  | e:(expr Atom) e':{"**" e':(expr Pow)}? when prio = Pow ->
      match e' with None -> e | Some e' -> e ** e'
  | e:(expr Pow) l:{fn:prod_sym e':(expr Pow)}**
                         when prio = Prod ->
      List.fold_left (fun acc (fn, e') -> fn acc e') e l
  | e:(expr Prod) l:{fn:sum_sym  e':(expr Prod)}*
                         when prio = Sum  ->
      List.fold_left (fun acc (fn, e') -> fn acc e') e l)

let blank = blank_regexp ''[ \t\r\n]*''
