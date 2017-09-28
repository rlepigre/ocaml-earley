open Generate_calc
open Earley
type calc_prio =
  | Sum 
  | Pro 
  | Pow 
  | Atm 
let prio_to_string =
  function | Sum  -> "Sum" | Pro  -> "Prod" | Pow  -> "Pow" | Atm  -> "Atom" 
let float_re = "[0-9]+\\([.][0-9]+\\)?\\([eE][-+]?[0-9]+\\)?" 
let float_num =
  Earley.apply (fun f  -> float_of_string f)
    (EarleyStr.regexp ~name:"float" float_re (fun groupe  -> groupe 0))
  
let pro_sym =
  Earley.alternatives
    [Earley.apply (fun _  -> ( *. )) (Earley.char '*' '*');
    Earley.apply (fun _  -> (/.)) (Earley.char '/' '/')]
  
let sum_sym =
  Earley.alternatives
    [Earley.apply (fun _  -> (+.)) (Earley.char '+' '+');
    Earley.apply (fun _  -> (-.)) (Earley.char '-' '-')]
  
let (expr,expr__set__grammar) = Earley.grammar_prio_family "expr" 
let expr __curry__varx0 __curry__varx1 __curry__prio =
  expr (__curry__varx0, __curry__varx1) __curry__prio 
let _ =
  expr__set__grammar
    (fun (op,cl)  ->
       ([(((fun _  -> true)), float_num);
        (((fun _  -> true)),
          (Earley.fsequence (Earley.char op op)
             (Earley.sequence (expr op cl Sum) (Earley.char cl cl)
                (fun e  -> fun _  -> fun _  -> e))));
        (((fun p  -> p <= Pow)),
          (Earley.sequence (Earley.char '-' '-') (expr op cl Pow)
             (fun _  -> fun e  -> -. e)));
        (((fun p  -> p <= Pow)),
          (Earley.sequence (Earley.char '+' '+') (expr op cl Pow)
             (fun _  -> fun e  -> e)));
        (((fun p  -> p <= Pow)),
          (Earley.fsequence (expr op cl Atm)
             (Earley.sequence (Earley.string "**" "**") (expr op cl Pow)
                (fun _  -> fun e'  -> fun e  -> e ** e'))));
        (((fun p  -> p <= Pro)),
          (Earley.fsequence (expr op cl Pro)
             (Earley.sequence pro_sym (expr op cl Pow)
                (fun fn  -> fun e'  -> fun e  -> fn e e'))));
        (((fun p  -> p <= Sum)),
          (Earley.fsequence (expr op cl Sum)
             (Earley.sequence sum_sym (expr op cl Pro)
                (fun fn  -> fun e'  -> fun e  -> fn e e'))))],
         (fun p  -> [])))
  
let _ = run (expr '(' ')' Sum) 
