open Camlp4.PreCast

let expr = Gram.Entry.mk "expr"

EXTEND Gram
  expr:
  [ "add" LEFTA
          [ x = expr; "+"; y = expr -> x +. y
          | x = expr; "-"; y = expr -> x -. y ]
  | "mult" LEFTA
           [ x = expr; "*"; y = expr -> x *. y
           | x = expr; "/"; y = expr -> x /. y ]
  | "pow" RIGHTA
	  [ x = expr; "**"; y = expr -> x ** y ]
  | "simple" NONA
             [ x = FLOAT -> float_of_string x
             | x = INT -> float_of_string x
             | "("; e = expr; ")" -> e ] ]
;
  END;;

let _ = 
  let x = Gram.parse expr Loc.ghost (Stream.of_channel stdin) in
  Printf.printf " => %f\n%!" x
