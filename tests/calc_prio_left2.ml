open Earley
open Generate_calc
type calc_prio =
  | Sum 
  | Prod 
  | Pow 
  | Atom 
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
let (expr_suit, expr_suit__set__grammar) = Earley.grammar_family "expr_suit"
let expr = Earley.declare_grammar "expr"
let _ =
  expr_suit__set__grammar
    (fun p ->
       Earley.alternatives
         ((if p >= Sum
           then
             [Earley.fsequence sum_sym
                (Earley.apply
                   (fun ((p', e') as _default_0) ->
                      fun fn ->
                        if p' <= Sum then give_up ();
                        (fun e -> (Sum, (fn e e')))) expr)]
           else []) @
            ((if p > Pow
              then
                [Earley.fsequence (Earley.string "**" "**")
                   (Earley.apply
                      (fun ((p', e') as _default_0) ->
                         fun _ ->
                           if p' < Pow then give_up ();
                           (fun e -> (Pow, (e ** e')))) expr)]
              else []) @
               ((if p >= Prod
                 then
                   [Earley.fsequence prod_sym
                      (Earley.apply
                         (fun ((p', e') as _default_0) ->
                            fun fn ->
                              if p' <= Prod then give_up ();
                              (fun e -> (Prod, (fn e e')))) expr)]
                 else []) @ []))))
let _ =
  Earley.set_grammar expr
    (Earley.alternatives
       [Earley.iter
          (Earley.apply
             (fun ((p, e) as _default_0) ->
                Earley.apply (fun g -> g e) (expr_suit p)) expr);
       Earley.apply (fun f -> (Atom, f)) float_num;
       Earley.fsequence (Earley.char '(' '(')
         (Earley.fsequence expr
            (Earley.apply
               (fun _ -> fun ((_, e) as _default_0) -> fun _ -> (Atom, e))
               (Earley.char ')' ')')));
       Earley.fsequence (Earley.char '-' '-')
         (Earley.apply
            (fun ((p, e) as _default_0) ->
               fun _ -> if p < Pow then give_up (); (Pow, (-. e))) expr);
       Earley.fsequence (Earley.char '+' '+')
         (Earley.apply
            (fun ((p, e) as _default_0) ->
               fun _ -> if p < Pow then give_up (); (Pow, e)) expr)])
let _ = run (apply snd expr)
