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

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> float
