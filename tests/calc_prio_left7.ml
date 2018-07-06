open Generate_calc
open Earley
type calc_prio =
  | Sum 
  | Pro 
  | Pow 
  | Atm 
let prio_to_string =
  function | Sum -> "Sum" | Pro -> "Prod" | Pow -> "Pow" | Atm -> "Atom"
let float_re = "[0-9]+\\([.][0-9]+\\)?\\([eE][-+]?[0-9]+\\)?"
let float_num =
  Earley.apply (fun f -> float_of_string f)
    (EarleyStr.regexp ~name:"float" float_re (fun groupe -> groupe 0))
let pro_sym =
  Earley.alternatives
    [Earley.apply (fun _ -> (/.)) (Earley.char '/' '/');
    Earley.apply (fun _ -> ( *. )) (Earley.char '*' '*')]
let sum_sym =
  Earley.alternatives
    [Earley.apply (fun _ -> (-.)) (Earley.char '-' '-');
    Earley.apply (fun _ -> (+.)) (Earley.char '+' '+')]
let (expr, expr__set__grammar) = Earley.grammar_prio_family "expr"
let expr __curry__varx0 __curry__varx1 __curry__prio =
  expr (__curry__varx0, __curry__varx1) __curry__prio
let _ =
  expr__set__grammar
    (fun (op, cl) ->
       ([(((fun p -> p <= Sum)),
           (Earley.fsequence (expr op cl Sum)
              (Earley.fsequence sum_sym
                 (Earley.apply (fun e' -> fun fn -> fun e -> fn e e')
                    (expr op cl Pro)))));
        (((fun _ -> true)), float_num);
        (((fun _ -> true)),
          (Earley.fsequence (Earley.char op op)
             (Earley.fsequence (expr op cl Sum)
                (Earley.apply (fun _ -> fun e -> fun _ -> e)
                   (Earley.char cl cl)))));
        (((fun p -> p <= Pow)),
          (Earley.fsequence (Earley.char '-' '-')
             (Earley.apply (fun e -> fun _ -> -. e) (expr op cl Pow))));
        (((fun p -> p <= Pow)),
          (Earley.fsequence (Earley.char '+' '+')
             (Earley.apply (fun e -> fun _ -> e) (expr op cl Pow))));
        (((fun p -> p <= Pow)),
          (Earley.fsequence (expr op cl Atm)
             (Earley.fsequence (Earley.string "**" "**")
                (Earley.apply (fun e' -> fun _ -> fun e -> e ** e')
                   (expr op cl Pow)))));
        (((fun p -> p <= Pro)),
          (Earley.fsequence (expr op cl Pro)
             (Earley.fsequence pro_sym
                (Earley.apply (fun e' -> fun fn -> fun e -> fn e e')
                   (expr op cl Pow)))))], (fun p -> [])))
let _ = run (expr '(' ')' Sum)
