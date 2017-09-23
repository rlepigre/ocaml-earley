open Earley
let g = Earley.declare_grammar "g" 
;;Earley.set_grammar g
    (Earley.apply (fun _default_0  -> ())
       (Earley.apply List.rev
          (Earley.fixpoint []
             (Earley.apply (fun x  -> fun y  -> x :: y)
                (Earley.alternatives
                   [Earley.apply (fun _  -> ()) (Earley.char ' ' ' ');
                   Earley.apply (fun _  -> ()) (Earley.char '\n' '\n');
                   Earley.apply (fun _  -> ()) (Earley.char '\t' '\t');
                   Earley.apply (fun _  -> ()) (Earley.char '\r' '\r')])))))
let blank = blank_grammar g no_blank 
let r = Earley.declare_grammar "r" 
;;Earley.set_grammar r
    (Earley.apply List.rev
       (Earley.fixpoint []
          (Earley.apply (fun x  -> fun y  -> x :: y)
             (Earley.alternatives
                [Earley.apply (fun _  -> ()) (Earley.char 'a' 'a');
                Earley.apply (fun _  -> ()) (Earley.char 'b' 'b')]))))
let patocomment = Earley.declare_grammar "patocomment" 
;;Earley.set_grammar patocomment
    (change_layout
       (Earley.fsequence (Earley.string "(*" "(*")
          (Earley.sequence
             (Earley.apply List.rev
                (Earley.fixpoint []
                   (Earley.apply (fun x  -> fun y  -> x :: y)
                      (Earley.alternatives
                         [Earley.apply (fun _  -> ())
                            (EarleyStr.regexp ~name:"[^*]" "[^*]"
                               (fun groupe  -> groupe 0));
                         Earley.apply (fun _  -> ()) (Earley.char '\n' '\n')]))))
             (Earley.string "*)" "*)") (fun _  -> fun _  -> fun _  -> ())))
       no_blank)
let patocomments = Earley.declare_grammar "patocomments" 
;;Earley.set_grammar patocomments
    (Earley.apply (fun _  -> ())
       (Earley.apply List.rev
          (Earley.fixpoint []
             (Earley.apply (fun x  -> fun y  -> x :: y) patocomment))))
let spaces = Earley.declare_grammar "spaces" 
;;Earley.set_grammar spaces
    (Earley.apply List.rev
       (Earley.fixpoint []
          (Earley.apply (fun x  -> fun y  -> x :: y)
             (EarleyStr.regexp ~name:"[ \\t\\r]" "[ \t\r]"
                (fun groupe  -> groupe 0)))))
let blank_grammar_sline = Earley.declare_grammar "blank_grammar_sline" 
;;Earley.set_grammar blank_grammar_sline
    (Earley.sequence spaces
       (Earley.option None
          (Earley.apply (fun x  -> Some x)
             (Earley.sequence (Earley.char '\n' '\n') spaces
                (fun _  -> fun _  -> ())))) (fun _  -> fun _  -> ()))
let blank_grammar_mline = Earley.declare_grammar "blank_grammar_mline" 
;;Earley.set_grammar blank_grammar_mline
    (Earley.sequence spaces
       (Earley.apply List.rev
          (Earley.fixpoint []
             (Earley.apply (fun x  -> fun y  -> x :: y)
                (Earley.sequence (Earley.char '\n' '\n') spaces
                   (fun _  -> fun _  -> ()))))) (fun _  -> fun _  -> ()))
let blank_sline = blank_grammar blank_grammar_sline no_blank 
let blank_mline = blank_grammar blank_grammar_mline no_blank 
let blank1 = blank_grammar patocomments blank_sline 
let blank2 = blank_grammar patocomments blank_mline 
open Common
let _ = parse_string r blank " a b a b b ab   ab bba " 
let _ = parse_string r blank1 "a  aab aa  a a a a\na b a ba b " 