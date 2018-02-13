open Earley
let g = Earley.declare_grammar "g" 
let _ =
  Earley.set_grammar g
    (Earley.apply (fun _default_0  -> ())
       (Earley.apply List.rev
          (Earley.fixpoint []
             (Earley.apply (fun x  -> fun y  -> x :: y)
                (Earley.alternatives
                   [Earley.apply (fun _  -> ()) (Earley.char '\r' '\r');
                   Earley.apply (fun _  -> ()) (Earley.char ' ' ' ');
                   Earley.apply (fun _  -> ()) (Earley.char '\n' '\n');
                   Earley.apply (fun _  -> ()) (Earley.char '\t' '\t')])))))
  
let blank = blank_grammar g no_blank 
let r = Earley.declare_grammar "r" 
let _ =
  Earley.set_grammar r
    (Earley.apply List.rev
       (Earley.fixpoint []
          (Earley.apply (fun x  -> fun y  -> x :: y)
             (Earley.alternatives
                [Earley.apply (fun _  -> ()) (Earley.char 'b' 'b');
                Earley.apply (fun _  -> ()) (Earley.char 'a' 'a')]))))
  
let patocomment = Earley.declare_grammar "patocomment" 
let _ =
  Earley.set_grammar patocomment
    (change_layout
       (Earley.fsequence (Earley.string "(*" "(*")
          (Earley.sequence
             (Earley.apply List.rev
                (Earley.fixpoint []
                   (Earley.apply (fun x  -> fun y  -> x :: y)
                      (Earley.alternatives
                         [Earley.apply (fun _  -> ()) (Earley.char '\n' '\n');
                         Earley.apply (fun _  -> ())
                           (EarleyStr.regexp
                              ~name:"[^*]\\\\|\\\\([*][^)]\\\\)"
                              "[^*]\\|\\([*][^)]\\)"
                              (fun groupe  -> groupe 0))]))))
             (Earley.string "*)" "*)") (fun _  -> fun _  -> fun _  -> ())))
       no_blank)
  
let patocomments = Earley.declare_grammar "patocomments" 
let _ =
  Earley.set_grammar patocomments
    (Earley.apply (fun _  -> ())
       (Earley.apply List.rev
          (Earley.fixpoint []
             (Earley.apply (fun x  -> fun y  -> x :: y) patocomment))))
  
let spaces = Earley.declare_grammar "spaces" 
let _ =
  Earley.set_grammar spaces
    (Earley.apply List.rev
       (Earley.fixpoint []
          (Earley.apply (fun x  -> fun y  -> x :: y)
             (EarleyStr.regexp ~name:"[ \\t\\r]" "[ \t\r]"
                (fun groupe  -> groupe 0)))))
  
let blank_grammar_sline = Earley.declare_grammar "blank_grammar_sline" 
let _ =
  Earley.set_grammar blank_grammar_sline
    (Earley.sequence spaces
       (Earley.option None
          (Earley.apply (fun x  -> Some x)
             (Earley.sequence (Earley.char '\n' '\n') spaces
                (fun _  -> fun _  -> ())))) (fun _  -> fun _  -> ()))
  
let blank_grammar_mline = Earley.declare_grammar "blank_grammar_mline" 
let _ =
  Earley.set_grammar blank_grammar_mline
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
let _ = parse_string r blank_sline " a b a b b ab\n   ab bba " 
let _ =
  try
    let _ = parse_string r blank_sline " a b a b b ab\n \n  ab bba "  in
    assert false
  with | Parse_error _ -> () 
let _ = parse_string r blank_mline " a b a b b\n ab\n \n  ab bba " 
let _ = parse_string r blank1 "a  aab aa  a a a a\na b(*to*to*) a ba b " 
let _ =
  try
    let _ = parse_string r blank1 " a b a b b ab\n (*to*to*)\n \n ab bba "
       in
    assert false
  with | Parse_error _ -> () 
let _ = parse_string r blank2 " a b a b b ab\n (*to*to*)\n \n ab bba " 
