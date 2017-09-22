open Decap

let parser g = {' ' | '\n' | '\t' | '\r'}* -> ()

let blank = blank_grammar g no_blank

let parser r = {'a' | 'b'}*

let _ = debug_lvl := 2
(*
let test = parse_string r blank " a b a b b ab   ab bba "
*)
let parser patocomment =
  (change_layout (
    parser
      _:"(*"
      _:{_:''[^*]'' | _:'\n'}*
      _:"*)"
  ) no_blank)

let parser patocomments =
  _:{patocomment}*

let parser spaces = ''[ \t\r]''*

let parser blank_grammar_sline =
  _:spaces _:{'\n' _:spaces}?

let parser blank_grammar_mline =
  _:spaces _:{'\n' _:spaces}*

let blank_sline = blank_grammar blank_grammar_sline no_blank
let blank_mline = blank_grammar blank_grammar_mline no_blank

let blank1 = blank_grammar patocomments blank_sline
let blank2 = blank_grammar patocomments blank_mline

let test = parse_string r blank1 "a  aab aa  a a a a\na b a ba b "