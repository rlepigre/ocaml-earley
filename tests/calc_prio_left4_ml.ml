open Earley
open Generate_calc
type calc_prio =
  | Sum 
  | Prod 
  | Pow 
  | Atom 
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
  
let expr = Earley.declare_grammar "expr" 
let (expr_lvl,expr_lvl__set__grammar) = Earley.grammar_family "expr_lvl" 
;;Earley.set_grammar expr
    (Earley.alternatives
       [Earley.apply (fun f  -> (Atom, f)) float_num;
       Earley.fsequence (Earley.char '(' '(')
         (Earley.sequence expr (Earley.char ')' ')')
            (fun ((_,e) as _default_0)  -> fun _  -> fun _  -> (Atom, e)));
       Earley.sequence (Earley.char '-' '-') (expr_lvl Pow)
         (fun _  -> fun e  -> (Pow, (-. e)));
       Earley.sequence (Earley.char '+' '+') (expr_lvl Pow)
         (fun _  -> fun e  -> (Pow, e));
       conditional_sequence expr
         (fun (p,e)  -> if p <= Pow then give_up (); e)
         (Earley.sequence (Earley.string "**" "**") (expr_lvl Pow)
            (fun _  -> fun _default_0  -> _default_0))
         (fun e  -> fun e'  -> (Pow, (e ** e')));
       conditional_sequence expr
         (fun (p,e)  -> if p < Prod then give_up (); e)
         (Earley.sequence prod_sym (expr_lvl Pow)
            (fun _default_1  -> fun _default_0  -> (_default_1, _default_0)))
         (fun e  -> fun (fn,e')  -> (Prod, (fn e e')));
       conditional_sequence expr
         (fun (p,e)  -> if p < Sum then give_up (); e)
         (Earley.sequence sum_sym (expr_lvl Prod)
            (fun _default_1  -> fun _default_0  -> (_default_1, _default_0)))
         (fun e  -> fun (fn,e')  -> (Sum, (fn e e')))])
;;expr_lvl__set__grammar
    (fun p  ->
       Earley.apply
         (fun ((p',e) as _default_0)  -> if p' < p then give_up (); e) expr)
let _ = run (apply snd expr) 
