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
  
let extra = ref [] 
let extra_expression p =
  Earley.alternatives (List.map (fun g  -> g p) (!extra)) 
let (expr,expr__set__grammar) = Earley.grammar_prio "expr" 
let _ =
  expr__set__grammar
    ([(((fun _  -> true)), float_num);
     (((fun _  -> true)),
       (Earley.fsequence (Earley.char '(' '(')
          (Earley.sequence (expr Sum) (Earley.char ')' ')')
             (fun e  -> fun _  -> fun _  -> e))));
     (((fun p  -> p <= Pow)),
       (Earley.sequence (Earley.char '-' '-') (expr Pow)
          (fun _  -> fun e  -> -. e)));
     (((fun p  -> p <= Pow)),
       (Earley.sequence (Earley.char '+' '+') (expr Pow)
          (fun _  -> fun e  -> e)));
     (((fun p  -> p <= Pow)),
       (Earley.fsequence (expr Atm)
          (Earley.sequence (Earley.string "**" "**") (expr Pow)
             (fun _  -> fun e'  -> fun e  -> e ** e'))));
     (((fun p  -> p <= Pro)),
       (Earley.fsequence (expr Pro)
          (Earley.sequence pro_sym (expr Pow)
             (fun fn  -> fun e'  -> fun e  -> fn e e'))));
     (((fun p  -> p <= Sum)),
       (Earley.fsequence (expr Sum)
          (Earley.sequence sum_sym (expr Pro)
             (fun fn  -> fun e'  -> fun e  -> fn e e'))))],
      (fun p  -> [extra_expression p]))
  
let _ = run (expr Sum) 
