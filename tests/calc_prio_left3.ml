open Generate_calc
open Earley
type calc_prio =
  | Sum 
  | Prod 
  | Pow 
  | Atom 
let prio_to_string =
  function
  | Sum  -> "Sum"
  | Prod  -> "Prod"
  | Pow  -> "Pow"
  | Atom  -> "Atom" 
let float_re = "[0-9]+\\([.][0-9]+\\)?\\([eE][-+]?[0-9]+\\)?" 
let float_num = Earley.declare_grammar "float_num" 
let _ =
  Earley.set_grammar float_num
    (Earley.apply (fun f  -> float_of_string f)
       (EarleyStr.regexp ~name:"float" float_re (fun groupe  -> groupe 0)))
  
let prod_sym = Earley.declare_grammar "prod_sym" 
let _ =
  Earley.set_grammar prod_sym
    (Earley.alternatives
       [Earley.apply (fun _  -> (/.)) (Earley.char '/' '/');
       Earley.apply (fun _  -> ( *. )) (Earley.char '*' '*')])
  
let sum_sym = Earley.declare_grammar "sum_sym" 
let _ =
  Earley.set_grammar sum_sym
    (Earley.alternatives
       [Earley.apply (fun _  -> (-.)) (Earley.char '-' '-');
       Earley.apply (fun _  -> (+.)) (Earley.char '+' '+')])
  
let (expr,set_expr) = grammar_family ~param_to_string:prio_to_string "expr" 
let _ =
  set_expr
    (fun prio  ->
       Earley.alternatives
         ((if prio = Sum then [expr Prod] else []) @
            ((if prio = Atom then [float_num] else []) @
               ((if prio = Atom
                 then
                   [Earley.fsequence (Earley.char '(' '(')
                      (Earley.sequence (expr Sum) (Earley.char ')' ')')
                         (fun e  -> fun _  -> fun _  -> e))]
                 else []) @
                  ((if prio = Pow
                    then
                      [Earley.sequence (Earley.char '-' '-') (expr Pow)
                         (fun _  -> fun e  -> -. e)]
                    else []) @
                     ((if prio = Pow
                       then
                         [Earley.sequence (Earley.char '+' '+') (expr Pow)
                            (fun _  -> fun e  -> e)]
                       else []) @
                        ((if prio = Pow
                          then
                            [Earley.sequence (expr Atom)
                               (Earley.option None
                                  (Earley.apply (fun x  -> Some x)
                                     (Earley.sequence
                                        (Earley.string "**" "**") (expr Pow)
                                        (fun _  ->
                                           fun _default_0  -> _default_0))))
                               (fun e  ->
                                  fun e'  ->
                                    match e' with
                                    | None  -> e
                                    | Some e' -> e ** e')]
                          else []) @
                           ((if prio = Prod
                             then
                               [Earley.fsequence (expr Prod)
                                  (Earley.sequence prod_sym (expr Pow)
                                     (fun fn  -> fun e'  -> fun e  -> fn e e'))]
                             else []) @
                              ((if prio = Sum
                                then
                                  [Earley.fsequence (expr Sum)
                                     (Earley.sequence sum_sym (expr Prod)
                                        (fun fn  ->
                                           fun e'  -> fun e  -> fn e e'))]
                                else []) @
                                 ((if prio = Prod then [expr Pow] else []) @
                                    []))))))))))
  
let _ = run (expr Sum) 
