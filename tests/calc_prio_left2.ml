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
    [Earley.apply (fun _  -> (/.)) (Earley.char '/' '/');
    Earley.apply (fun _  -> ( *. )) (Earley.char '*' '*')]
  
let sum_sym =
  Earley.alternatives
    [Earley.apply (fun _  -> (-.)) (Earley.char '-' '-');
    Earley.apply (fun _  -> (+.)) (Earley.char '+' '+')]
  
let (expr_suit,expr_suit__set__grammar) = Earley.grammar_family "expr_suit" 
let expr = Earley.declare_grammar "expr" 
let _ =
  expr_suit__set__grammar
    (fun p  ->
       Earley.alternatives
         ((if p >= Sum
           then
             [Earley.sequence sum_sym expr
                (fun fn  ->
                   fun ((p',e') as _default_0)  ->
                     if p' <= Sum then give_up ();
                     (fun e  -> (Sum, (fn e e'))))]
           else []) @
            ((if p > Pow
              then
                [Earley.sequence (Earley.string "**" "**") expr
                   (fun _  ->
                      fun ((p',e') as _default_0)  ->
                        if p' < Pow then give_up ();
                        (fun e  -> (Pow, (e ** e'))))]
              else []) @
               ((if p >= Prod
                 then
                   [Earley.sequence prod_sym expr
                      (fun fn  ->
                         fun ((p',e') as _default_0)  ->
                           if p' <= Prod then give_up ();
                           (fun e  -> (Prod, (fn e e'))))]
                 else []) @ []))))
  
let _ =
  Earley.set_grammar expr
    (Earley.alternatives
       [Earley.iter
          (Earley.apply
             (fun ((p,e) as _default_0)  ->
                Earley.apply (fun g  -> g e) (expr_suit p)) expr);
       Earley.apply (fun f  -> (Atom, f)) float_num;
       Earley.fsequence (Earley.char '(' '(')
         (Earley.sequence expr (Earley.char ')' ')')
            (fun ((_,e) as _default_0)  -> fun _  -> fun _  -> (Atom, e)));
       Earley.sequence (Earley.char '-' '-') expr
         (fun _  ->
            fun ((p,e) as _default_0)  ->
              if p < Pow then give_up (); (Pow, (-. e)));
       Earley.sequence (Earley.char '+' '+') expr
         (fun _  ->
            fun ((p,e) as _default_0)  ->
              if p < Pow then give_up (); (Pow, e))])
  
let _ = run (apply snd expr) 
