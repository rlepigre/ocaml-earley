open Decap

let parser g = {' ' | '\n' | '\t' | '\r'}* -> ()

let blank = blank_grammar g no_blank

let parser r = {'a' | 'b'}*

let _ = debug_lvl := 200
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

let patocomments =
  parser _:{patocomment}*

let parser spaces = ''[ \t\r]''

let blank_grammar_sline =
  parser _:spaces _:{'\n' _:spaces}?

let blank_grammar_mline =
  parser _:spaces _:{'\n' _:spaces}*

let blank_sline = blank_grammar blank_grammar_sline no_blank
let blank_mline = blank_grammar blank_grammar_mline no_blank

let blank1 = blank_grammar patocomments blank_sline
let blank2 = blank_grammar patocomments blank_mline

let test = parse_string r blank_sline "      a b a b b ab   ab bba "
