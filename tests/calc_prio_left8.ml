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
let extra = ref []
let extra_expression p =
  Earley.alternatives (List.map (fun g -> g p) (!extra))
let (expr_aux, expr_aux__set__grammar) = Earley.grammar_prio "expr_aux"
let (expr, expr__set__grammar) = Earley.grammar_family "expr"
let _ =
  expr_aux__set__grammar
    ([(((fun p -> p <= Sum)),
        (Earley.fsequence (expr Sum)
           (Earley.fsequence sum_sym
              (Earley.apply (fun e' -> fun fn -> fun e -> fn e e') (expr Pro)))));
     (((fun _ -> true)), float_num);
     (((fun _ -> true)),
       (Earley.fsequence (Earley.char '(' '(')
          (Earley.fsequence (expr Sum)
             (Earley.apply (fun _ -> fun e -> fun _ -> e)
                (Earley.char ')' ')')))));
     (((fun p -> p <= Pow)),
       (Earley.fsequence (Earley.char '-' '-')
          (Earley.apply (fun e -> fun _ -> -. e) (expr Pow))));
     (((fun p -> p <= Pow)),
       (Earley.fsequence (Earley.char '+' '+')
          (Earley.apply (fun e -> fun _ -> e) (expr Pow))));
     (((fun p -> p <= Pow)),
       (Earley.fsequence (expr Atm)
          (Earley.fsequence (Earley.string "**" "**")
             (Earley.apply (fun e' -> fun _ -> fun e -> e ** e') (expr Pow)))));
     (((fun p -> p <= Pro)),
       (Earley.fsequence (expr Pro)
          (Earley.fsequence pro_sym
             (Earley.apply (fun e' -> fun fn -> fun e -> fn e e') (expr Pow)))))],
      (fun p -> []))
let _ =
  expr__set__grammar
    (fun p -> Earley.alternatives [expr_aux p; extra_expression p])
let _ = run (expr Sum)
