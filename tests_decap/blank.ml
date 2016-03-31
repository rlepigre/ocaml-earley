open Decap

let parser g = {' ' | '\n' | '\t' | '\r'}* -> ()

let blank = blank_grammar g no_blank

let parser r = {'a' | 'b'}*

let _ = debug_lvl := 2

let test = parse_string r blank " a b a b b ab   ab bba "
