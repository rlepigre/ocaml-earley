open Earley
open Generate_calc
open Common
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
let float_num =
  Earley.apply (fun f  -> float_of_string f)
    (EarleyStr.regexp ~name:"float" float_re (fun groupe  -> groupe 0))
  
let prod_sym =
  Earley.alternatives
    [Earley.apply (fun _  -> ( *. )) (Earley.char '*' '*');
    Earley.apply (fun _  -> (/.)) (Earley.char '/' '/')]
  
let sum_sym =
  Earley.alternatives
    [Earley.apply (fun _  -> (+.)) (Earley.char '+' '+');
    Earley.apply (fun _  -> (-.)) (Earley.char '-' '-')]
  
let test = Earley.declare_grammar "test" 
;;Earley.set_grammar test
    (Earley.alternatives
       [Earley.apply (fun _  -> ()) (Earley.empty ());
       Earley.sequence test (Earley.char 'a' 'a')
         (fun _default_0  -> fun _  -> _default_0)])
let (expr,set_expr) = grammar_family ~param_to_string:prio_to_string "expr" 
let _ =
  set_expr
    (fun prio  ->
       Earley.alternatives (float_num ::
         (Earley.fsequence (Earley.char '(' '(')
            (Earley.sequence (expr Sum) (Earley.char ')' ')')
               (fun e  -> fun _  -> fun _  -> e))) ::
         (let y =
            let y =
              let y =
                let y =
                  let y = []  in
                  if prio <= Sum
                  then
                    (Earley.fsequence (expr Sum)
                       (Earley.sequence sum_sym (expr Prod)
                          (fun fn  -> fun e'  -> fun e  -> fn e e')))
                    :: y
                  else y  in
                if prio <= Prod
                then
                  (Earley.fsequence (expr Prod)
                     (Earley.sequence prod_sym (expr Pow)
                        (fun fn  -> fun e'  -> fun e  -> fn e e')))
                  :: y
                else y  in
              if prio <= Pow
              then
                (Earley.fsequence (expr Atom)
                   (Earley.sequence (Earley.string "**" "**") (expr Pow)
                      (fun _  -> fun e'  -> fun e  -> e ** e')))
                :: y
              else y  in
            if prio <= Pow
            then
              (Earley.sequence (Earley.char '+' '+') (expr Pow)
                 (fun _  -> fun e  -> e))
              :: y
            else y  in
          if prio <= Pow
          then
            (Earley.sequence (Earley.char '-' '-') (expr Pow)
               (fun _  -> fun e  -> -. e))
            :: y
          else y)))
  
let _ = run (expr Sum) 
