open Earley
let gamma3 = Earley.declare_grammar "gamma3" 
let _ =
  Earley.set_grammar gamma3
    (Earley.alternatives
       [Earley.fsequence gamma3
          (Earley.sequence gamma3 gamma3
             (fun _default_1  -> fun _default_0  -> fun _default_2  -> ()));
       Earley.apply (fun _  -> ()) (Earley.char 'a' 'a');
       Earley.sequence gamma3 gamma3
         (fun _default_1  -> fun _default_0  -> ())])
  
let n = int_of_string (Sys.argv.(1)) 
let input = String.make n 'a' 
let _ = Earley.debug_lvl := 0; Earley.warn_merge := false 
let _ = parse_string gamma3 no_blank input 
