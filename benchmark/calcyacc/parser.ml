type token =
  | FLOAT of (float)
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | POW
  | LPAREN
  | RPAREN
  | EOL

open Parsing;;
let _ = parse_error;;
let yytransl_const = [|
  258 (* PLUS *);
  259 (* MINUS *);
  260 (* TIMES *);
  261 (* DIV *);
  262 (* POW *);
  263 (* LPAREN *);
  264 (* RPAREN *);
  265 (* EOL *);
    0|]

let yytransl_block = [|
  257 (* FLOAT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\000\000"

let yylen = "\002\000\
\002\000\001\000\003\000\003\000\003\000\003\000\003\000\003\000\
\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\002\000\000\000\000\000\000\000\011\000\000\000\
\010\000\009\000\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\003\000\000\000\000\000\000\000\000\000\000\000"

let yydgoto = "\002\000\
\007\000\008\000"

let yysindex = "\005\000\
\059\255\000\000\000\000\059\255\059\255\059\255\000\000\011\255\
\000\000\000\000\051\255\059\255\059\255\059\255\059\255\059\255\
\000\000\000\000\255\254\255\254\001\255\001\255\001\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\039\255\043\255\019\255\027\255\035\255"

let yygindex = "\000\000\
\000\000\252\255"

let yytablesize = 66
let yytable = "\009\000\
\010\000\011\000\014\000\015\000\016\000\001\000\016\000\019\000\
\020\000\021\000\022\000\023\000\012\000\013\000\014\000\015\000\
\016\000\000\000\000\000\017\000\006\000\006\000\006\000\006\000\
\000\000\000\000\006\000\006\000\007\000\007\000\007\000\007\000\
\000\000\000\000\007\000\007\000\008\000\008\000\008\000\008\000\
\004\000\004\000\008\000\008\000\005\000\005\000\004\000\004\000\
\000\000\000\000\005\000\005\000\012\000\013\000\014\000\015\000\
\016\000\000\000\018\000\003\000\004\000\005\000\000\000\000\000\
\000\000\006\000"

let yycheck = "\004\000\
\005\000\006\000\004\001\005\001\006\001\001\000\006\001\012\000\
\013\000\014\000\015\000\016\000\002\001\003\001\004\001\005\001\
\006\001\255\255\255\255\009\001\002\001\003\001\004\001\005\001\
\255\255\255\255\008\001\009\001\002\001\003\001\004\001\005\001\
\255\255\255\255\008\001\009\001\002\001\003\001\004\001\005\001\
\002\001\003\001\008\001\009\001\002\001\003\001\008\001\009\001\
\255\255\255\255\008\001\009\001\002\001\003\001\004\001\005\001\
\006\001\255\255\008\001\001\001\002\001\003\001\255\255\255\255\
\255\255\007\001"

let yynames_const = "\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  POW\000\
  LPAREN\000\
  RPAREN\000\
  EOL\000\
  "

let yynames_block = "\
  FLOAT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 14 "parser.mly"
                                    ( _1 )
# 104 "parser.ml"
               : float))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 17 "parser.mly"
                                    ( _1 )
# 111 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 18 "parser.mly"
                                    ( _2 )
# 118 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 19 "parser.mly"
                                    ( _1 +. _3 )
# 126 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 20 "parser.mly"
                                    ( _1 -. _3 )
# 134 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 21 "parser.mly"
                                    ( _1 *. _3 )
# 142 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 22 "parser.mly"
                                    ( _1 /. _3 )
# 150 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 23 "parser.mly"
                                    ( _1 ** _3 )
# 158 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 24 "parser.mly"
                                    ( -. _2 )
# 165 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 25 "parser.mly"
                                   ( -. _2 )
# 172 "parser.ml"
               : 'expr))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : float)
