open Generate_calc
open Earley
type calc_prio =
  | Sum 
  | Prod 
  | Pow 
  | Atom 
let prio_to_string =
  function | Sum -> "Sum" | Prod -> "Prod" | Pow -> "Pow" | Atom -> "Atom"
let float_re = "[0-9]+\\([.][0-9]+\\)?\\([eE][-+]?[0-9]+\\)?"
let float_num =
  Earley.apply (fun f -> float_of_string f)
    (EarleyStr.regexp ~name:"float" float_re (fun groupe -> groupe 0))
let prod_sym =
  Earley.alternatives
    [Earley.apply (fun _ -> (/.)) (Earley.char '/' '/');
    Earley.apply (fun _ -> ( *. )) (Earley.char '*' '*')]
let sum_sym =
  Earley.alternatives
    [Earley.apply (fun _ -> (-.)) (Earley.char '-' '-');
    Earley.apply (fun _ -> (+.)) (Earley.char '+' '+')]
let (expr, set_expr) = grammar_family ~param_to_string:prio_to_string "expr"
let _ =
  set_expr
    (fun prio ->
       Earley.alternatives
         ((if prio = Sum then [expr Prod] else []) @
            ((if prio = Atom then [float_num] else []) @
               ((if prio = Atom
                 then
                   [Earley.fsequence (Earley.char '(' '(')
                      (Earley.fsequence (expr Sum)
                         (Earley.apply (fun _ -> fun e -> fun _ -> e)
                            (Earley.char ')' ')')))]
                 else []) @
                  ((if prio = Pow
                    then
                      [Earley.fsequence (Earley.char '-' '-')
                         (Earley.apply (fun e -> fun _ -> -. e) (expr Pow))]
                    else []) @
                     ((if prio = Pow
                       then
                         [Earley.fsequence (Earley.char '+' '+')
                            (Earley.apply (fun e -> fun _ -> e) (expr Pow))]
                       else []) @
                        ((if prio = Pow
                          then
                            [Earley.fsequence (expr Atom)
                               (Earley.fsequence (Earley.string "**" "**")
                                  (Earley.apply
                                     (fun e' -> fun _ -> fun e -> e ** e')
                                     (expr Pow)))]
                          else []) @
                           ((if prio = Pow then [expr Atom] else []) @
                              ((if prio = Prod
                                then
                                  [Earley.fsequence (expr Prod)
                                     (Earley.fsequence prod_sym
                                        (Earley.apply
                                           (fun e' ->
                                              fun fn -> fun e -> fn e e')
                                           (expr Pow)))]
                                else []) @
                                 ((if prio = Sum
                                   then
                                     [Earley.fsequence (expr Sum)
                                        (Earley.fsequence sum_sym
                                           (Earley.apply
                                              (fun e' ->
                                                 fun fn -> fun e -> fn e e')
                                              (expr Prod)))]
                                   else []) @
                                    ((if prio = Prod then [expr Pow] else [])
                                       @ [])))))))))))
let _ = run (expr Sum)
