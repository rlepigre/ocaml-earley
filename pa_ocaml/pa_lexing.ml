open Earley_core

(** Representation of a buffer with a specific position. *)
type buf_pos = Input.buffer * int

(** {2 Comments and documentation comments} *********************************)

(** Exception [Unclosed_comment(in_str, buf, pos)] is raised when a comment at
    is not closed properly at position [pos] in buffer [buf]. Note that if the
    [in_str] is set to [true] then the problem is due to an unclosed string in
    a comment. *)
exception Unclosed_comment of bool * Input.buffer * int

(** [unclosed_comment ~in_str (buf, pos)] signals an unclodes comment. *)
let unclosed_comment : ?in_str:bool -> buf_pos -> 'a =
  fun ?(in_str=false) (buf, pos) -> raise (Unclosed_comment(in_str, buf, pos))

(** Representation of a documentation comment. *)
type doc_comment =
  { doc_start : buf_pos
  ; doc_end   : buf_pos
  ; doc_text  : string }

(** [doc_comments] holds documentation comments that have already been parsed,
    but only at the current level. *)
let doc_comments : doc_comment list ref = ref []

(** [doc_stack] is used to store documentation comment contexts that are in an
    outer scope (e.g., a parrent module). *)
let doc_stack : doc_comment list list ref = ref []

(** [push_comments ()] pushes the current documentation comments to the stack,
    and reinitialises the current comments. This function is used whenever the
    parser enters the scope of a new module/signature definition. *)
let push_comments : unit -> unit = fun _ ->
  doc_stack := !doc_comments :: !doc_stack; doc_comments := []

(** [pop_comments ()] pops back the documentation comments stored in the stack
    (thus overwriting the currently stored documentation comments).  Note that
    this function is used when getting out of a module definition. *)
let pop_comments : unit -> unit = fun _ ->
  match !doc_stack with
  | []       -> assert false (* Does not happen: always well-bracketed. *)
  | c::stack -> doc_comments := !doc_comments @ c; doc_stack := stack

(** [ocaml_blank buf pos] is the Earley blank function for OCaml, that ignores
    blanks starting at buffer [buf] and position [pos]. The ignored characters
    include [' '], ['\t'], ['\r'], ['\n'], everything enclosed between  ["(*"]
    and ["*)"] (multi-line comments). Multi-line comments can contain (nested)
    multi-line comments,  as well as valid string litterals (including strings
    such as ["(*"] or ["*)"]). *)
let ocaml_blank : Earley.blank = fun buf pos ->
  let odoc = ref false in
  let odoc_buf = Buffer.create 1024 in
  let rec fn state stack prev ((buf, pos) as curr) =
    let (c, buf', pos') = Input.read buf pos in
    if !odoc then Buffer.add_char odoc_buf c;
    let next = (buf', pos') in
    match (state, stack, c) with
    (* Basic blancs. *)
    | (`Ini      , []  , ' '     )
    | (`Ini      , []  , '\t'    )
    | (`Ini      , []  , '\r'    )
    | (`Ini      , []  , '\n'    ) -> fn `Ini stack curr next
    (* Comment opening. *)
    | (`Ini      , _   , '('     ) -> fn (`Opn(curr)) stack curr next
    | (`Ini      , []  , _       ) -> curr
    | (`Opn(p)   , []  , '*'     ) ->
        (* Potential documentation comment. *)
        let (c1, buf', pos') = Input.read buf' pos' in
        let is_doc = c1 = '*' && Input.get buf' pos' <> '*' in
        if is_doc then (odoc := true; fn `Cls [p] curr (buf', pos'))
        else fn `Ini [p] curr next
    | (`Opn(p)   , _   , '*'     ) -> fn `Ini (p::stack) curr next
    | (`Opn(_)   , _::_, '"'     ) -> fn (`Str(curr)) stack curr next (*#*)
    | (`Opn(_)   , _::_, '{'     ) -> fn (`SOp([],curr)) stack curr next (*#*)
    | (`Opn(_)   , _::_, '('     ) -> fn (`Opn(curr)) stack curr next
    | (`Opn(_)   , []  , _       ) -> prev
    | (`Opn(_)   , _   , _       ) -> fn `Ini stack curr next
    (* String litteral in a comment (including the # rules). *)
    | (`Ini      , _::_, '"'     ) -> fn (`Str(curr)) stack curr next
    | (`Str(_)   , _::_, '"'     ) -> fn `Ini stack curr next
    | (`Str(p)   , _::_, '\\'    ) -> fn (`Esc(p)) stack curr next
    | (`Esc(p)   , _::_, _       ) -> fn (`Str(p)) stack curr next
    | (`Str(p)   , _::_, '\255'  ) -> unclosed_comment ~in_str:true p
    | (`Str(_)   , _::_, _       ) -> fn state stack curr next
    | (`Str(_)   , []  , _       ) -> assert false (* Impossible. *)
    | (`Esc(_)   , []  , _       ) -> assert false (* Impossible. *)
    (* Delimited string litteral in a comment. *)
    | (`Ini      , _::_, '{'     ) -> fn (`SOp([],curr)) stack curr next
    | (`SOp(l ,p), _::_, 'a'..'z')
    | (`SOp(l ,p), _::_, '_'     ) -> fn (`SOp(c::l,p)) stack curr next
    | (`SOp(_ ,_), p::_, '\255'  ) -> unclosed_comment p
    | (`SOp(l ,p), _::_, '|'     ) -> fn (`SIn(List.rev l,p)) stack curr next
    | (`SOp(_ ,_), _::_, _       ) -> fn `Ini stack curr next
    | (`SIn(l ,p), _::_, '|'     ) -> fn (`SCl(l,(l,p))) stack curr next
    | (`SIn(_ ,p), _::_, '\255'  ) -> unclosed_comment ~in_str:true p
    | (`SIn(_ ,_), _::_, _       ) -> fn state stack curr next
    | (`SCl([],b), _::_, '}'     ) -> fn `Ini stack curr next
    | (`SCl([],b), _::_, '\255'  ) -> unclosed_comment ~in_str:true (snd b)
    | (`SCl([],b), _::_, _       ) -> fn (`SIn(b)) stack curr next
    | (`SCl(l ,b), _::_, c       ) ->
        if c = List.hd l then fn (`SCl(List.tl l, b)) stack curr next
        else fn (`SIn(b)) stack curr next
    | (`SOp(_ ,_), []  , _       ) -> assert false (* Impossible. *)
    | (`SIn(_ ,_), []  , _       ) -> assert false (* Impossible. *)
    | (`SCl(_ ,_), []  , _       ) -> assert false (* Impossible. *)
    (* Comment closing. *)
    | (`Ini      , _::_, '*'     ) -> fn `Cls stack curr next
    | (`Cls      , _::_, '*'     ) -> fn `Cls stack curr next
    | (`Cls      , _::_, '"'     ) -> fn (`Str(curr)) stack curr next (*#*)
    | (`Cls      , _::_, '{'     ) -> fn (`SOp([],curr)) stack curr next (*#*)
    | (`Cls      , p::s, ')'     ) ->
        (* Potential end of documentation comment. *)
        if !odoc && s = [] then
          begin
            (* Get the comment text, reset the buffer. *)
            let text = Buffer.sub odoc_buf 0 (Buffer.length odoc_buf - 2) in
            Buffer.clear odoc_buf;
            let c = {doc_start = p; doc_end = next; doc_text = text} in
            doc_comments := c :: !doc_comments;
            odoc := false
          end;
        fn `Ini s curr next
    | (`Cls      , _::_, _       ) -> fn `Ini stack curr next
    | (`Cls      , []  , _       ) -> assert false (* Impossible. *)
    (* Comment contents (excluding string litterals). *)
    | (`Ini      , p::_, '\255'  ) -> unclosed_comment p
    | (`Ini      , _::_, _       ) -> fn `Ini stack curr next
  in
  fn `Ini [] (buf, pos) (buf, pos)

(** {2 Keywords management} *************************************************)

(** [is_identifier_char c] tells whether [c] could appear in an identifier. *)
let is_identifier_char : char -> bool = fun c ->
  match c with
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true
  | _                                           -> false

(** [keyword s] creates a keyword parser for [s]. *)
let key_word s =
  if String.length s <= 0 then invalid_arg "Pa_lexing.key_word";
  Earley.keyword s is_identifier_char ()

(** {3 Keyword declarations} *)

let mutable_kw     = key_word "mutable"
let private_kw     = key_word "private"
let virtual_kw     = key_word "virtual"
let rec_kw         = key_word "rec"
let to_kw          = key_word "to"
let downto_kw      = key_word "downto"
let joker_kw       = key_word "_"
let method_kw      = key_word "method"
let object_kw      = key_word "object"
let class_kw       = key_word "class"
let inherit_kw     = key_word "inherit"
let as_kw          = key_word "as"
let of_kw          = key_word "of"
let module_kw      = key_word "module"
let open_kw        = key_word "open"
let include_kw     = key_word "include"
let type_kw        = key_word "type"
let val_kw         = key_word "val"
let external_kw    = key_word "external"
let constraint_kw  = key_word "constraint"
let begin_kw       = key_word "begin"
let end_kw         = key_word "end"
let and_kw         = key_word "and"
let true_kw        = key_word "true"
let false_kw       = key_word "false"
let exception_kw   = key_word "exception"
let when_kw        = key_word "when"
let fun_kw         = key_word "fun"
let function_kw    = key_word "function"
let let_kw         = key_word "let"
let in_kw          = key_word "in"
let initializer_kw = key_word "initializer"
let with_kw        = key_word "with"
let while_kw       = key_word "while"
let for_kw         = key_word "for"
let do_kw          = key_word "do"
let done_kw        = key_word "done"
let new_kw         = key_word "new"
let assert_kw      = key_word "assert"
let if_kw          = key_word "if"
let then_kw        = key_word "then"
let else_kw        = key_word "else"
let try_kw         = key_word "try"
let match_kw       = key_word "match"
let struct_kw      = key_word "struct"
let functor_kw     = key_word "functor"
let sig_kw         = key_word "sig"
let lazy_kw        = key_word "lazy"
let parser_kw      = key_word "parser"
let cached_kw      = key_word "cached"

(** [mutable_flag] is a parser for an optional "mutable" keyword. *)
let parser mutable_flag : Asttypes.mutable_flag Earley.grammar =
  | mutable_kw -> Asttypes.Mutable
  | EMPTY      -> Asttypes.Immutable

(** [private_flag] is a parser for an optional "private" keyword. *)
let parser private_flag : Asttypes.private_flag Earley.grammar =
  | private_kw -> Asttypes.Private
  | EMPTY      -> Asttypes.Public

(** [virtual_flag] is a parser for an optional "virtual" keyword. *)
let parser virtual_flag : Asttypes.virtual_flag Earley.grammar =
  | virtual_kw -> Asttypes.Virtual
  | EMPTY      -> Asttypes.Concrete

(** [rec_flag] is a parser for an optional "rec" keyword. *)
let parser rec_flag : Asttypes.rec_flag Earley.grammar =
  | rec_kw -> Asttypes.Recursive
  | EMPTY  -> Asttypes.Nonrecursive

(** [downto_flag] is a parser for either a "to" or a "downto" keyword. *)
let parser downto_flag : Asttypes.direction_flag Earley.grammar =
  | to_kw     -> Asttypes.Upto
  | downto_kw -> Asttypes.Downto

(** {3 Some parsers to forbid keywords} *)

(** [not_keyword s] fails if the input matches keyword [s], and does not parse
    any input (i.e., this is only a test combinator). *)
let no_keyword : string -> unit Earley.grammar = fun s ->
  let len = String.length s in
  let rec fn i buf pos =
    let (c, buf, pos) = Input.read buf pos in
    if i >= len then ((), is_identifier_char c)
    else if c <> s.[i] then ((), true) else fn (i + 1) buf pos
  in
  Earley.test ~name:("no_" ^ s) Charset.full (fn 0)

let no_else   = no_keyword "else"
let no_with   = no_keyword "with"
let no_parser = no_keyword "parser"

(** {3 Other similar functions for reserved sequences} *)

(** [no_dot] is a grammar that fails if the next character is ['.']. Note that
    not input is consumed, whatever the outcome of the test. *)
let no_dot : unit Earley.grammar =
  let fn buf pos = ((), Input.get buf pos <> '.') in
  Earley.test ~name:"no_dot" Charset.full fn

(** [no_semi] is a grammar that fails if the next character is a [';'], except
    if the second next character is also [';']. No input is consumed. *)
let no_semi : unit Earley.grammar =
  let fn buf pos =
    let (c, buf, pos) = Input.read buf pos in
    ((), c <> ';' || Input.get buf pos = ';')
  in
  Earley.test ~name:"no_semi" Charset.full fn

(** [no_semi] is a grammar that fails if the next character is a [':'], except
    if the second next character is also [':']. No input is consumed. *)
let no_colon : unit Earley.grammar =
  let fn buf pos =
    let (c, buf, pos) = Input.read buf pos in
    ((), c <> ':' || Input.get buf pos = ':')
  in
  Earley.test ~name:"no_colon" Charset.full fn

(** {2 Identifiers} *********************************************************)

(** [make_reserved l] initializes a structure for storing a list of (reserved)
    strings to [l], and returns a pair of functions [(mem, add)], respectively
    testing the membership of a string and adding a new reserved element. *)
let make_reserved : string list -> (string->bool) * (string->unit) = fun l ->
  let htbl = Hashtbl.create 37 in
  List.iter (fun s -> Hashtbl.add htbl s s) l;
  (Hashtbl.mem htbl, (fun s -> Hashtbl.add htbl s s))

(** Functions for manipulating reserved identifiers (e.g., keywords). *)
let (is_reserved_id, add_reserved_id) = make_reserved
  [ "and" ; "as" ; "assert" ; "asr" ; "begin" ; "class" ; "constraint" ; "do"
  ; "done" ; "downto" ; "else" ; "end" ; "exception" ; "external" ; "false"
  ; "for" ; "function" ; "functor" ; "fun" ; "if" ; "in" ; "include"
  ; "inherit" ; "initializer" ; "land" ; "lazy" ; "let" ; "lor" ; "lsl"
  ; "lsr" ; "lxor" ; "match" ; "method" ; "mod" ; "module" ; "mutable"
  ; "new" ; "object" ; "of" ; "open" ; "or" ; "private" ; "rec" ; "sig"
  ; "struct" ; "then" ; "to" ; "true" ; "try" ; "type" ; "val" ; "virtual"
  ; "when" ; "while" ; "with" ; "_" ]

(** Functions for manipulating reserved symbols. *)
let (is_reserved_symb, add_reserved_symb) = make_reserved
  [ "#" ; "'" ; "(" ; ")" ; "," ; "->" ; "->>"; "." ; ".." ; ":" ; ":>" ; ";"
  ; ";;" ; "<-" ; ">]" ; ">}" ; "?" ; "[" ; "[<" ; "[>" ; "[|" ; "]" ; "_"
  ; "`" ; "{" ; "{<" ; "|" ; "|]" ; "}" ; "~"; "$" ]

(** [ident] is a grammar that accepts any lowercase or upercase identifier, as
    long as it is not reserved according to the [is_reserved_id] function. *)
let parser ident = id:''[A-Za-z_][a-zA-Z0-9_']*'' ->
  if is_reserved_id id then Earley.give_up (); id

(** [lident] is a grammar that accepts any non-reserved, lowercase identifier.
    Reserved identifiers are identified using [is_reserved_id]. *)
let parser lident = id:''[a-z_][a-zA-Z0-9_']*'' ->
  if is_reserved_id id then Earley.give_up (); id

(** [uident] is a grammar that accepts any uppercase identifier. *)
let parser uident = ''[A-Z][a-zA-Z0-9_']*''

(** {3 Special characters and delimiters} *)

(** [not_special] can be used to reject the current input if it is immediately
    followed by a special (infix or prefix operator) character. In the process
    no blank characters are ignored prior to testing. *)
let not_special : unit Earley.grammar =
  let cs = ref Charset.empty in
  String.iter (fun c -> cs := Charset.add !cs c) "!$%&*+./:<=>?@^|~-";
  Earley.blank_not_in_charset ~name:"not_special" !cs

(** [single_char c] is a grammar that accepts a single [c] character, but that
    rejects the input if it is then again followed by [c]. *)
let single_char : char -> unit Earley.grammar = fun c ->
  let fn str pos =
    let (c_read, str, pos) = Input.read str pos in
    if c <> c_read || Input.get str pos = c then Earley.give_up ();
    ((), str, pos)
  in
  Earley.black_box fn (Charset.singleton c) false (String.make 1 c)

(** [double_char c] is a grammar that accepts a sequence of (exactly) two [c].
    If a third [c] follows, the input is rejected. *)
let double_char : char -> unit Earley.grammar = fun c ->
  let fn str pos =
    let (c_read, str, pos) = Input.read str pos in
    if c_read <> c then Earley.give_up ();
    let (c_read, str, pos) = Input.read str pos in
    if c_read <> c || Input.get str pos = c then Earley.give_up ();
    ((), str, pos)
  in
  Earley.black_box fn (Charset.singleton c) false (String.make 2 c)

let semi_col        = single_char ';'
let double_semi_col = double_char ';'
let single_quote    = single_char '\''
let double_quote    = double_char '\''

(** {2 Constants and litterals} *********************************************)

(** [union_re l] builds the string representation (following [Str] syntax]) of
    a regular expression that is the alternative of the regular expressions in
    the list [l]. *)
let union_re : string list -> string = fun l ->
  String.concat "\\|" (List.map (Printf.sprintf "\\(%s\\)") l)

(** [cs_to_string cs] converts a list of characters into a string. *)
let cs_to_string : char list -> string =
  let b = Buffer.create 27 in
  fun cs -> Buffer.(clear b; List.iter (add_char b) cs; contents b)

(** [bool_lit] accepts a single boolean litteral. *)
let parser bool_lit : string Earley.grammar =
  | false_kw -> "false"
  | true_kw  -> "true"

(** {3 Numerical constants} *)

(** [num_suffix] accepts an optional numerical suffix character. *)
let num_suffix : char option Earley.grammar =
  let suffix_cs = Charset.(union (range 'g' 'z') (range 'G' 'Z')) in
  let no_suffix_cs = List.fold_left Charset.add suffix_cs ['.'; 'e'; 'E'] in
  let no_suffix buf pos _ _ =
    ((), not (Charset.mem no_suffix_cs (Input.get buf pos)))
  in
  parser
  | - s:(Earley.in_charset suffix_cs)            -> Some s
  | _:(Earley.blank_test Charset.full no_suffix) -> None

(** [int_litteral] accepts an integer litteral in any valid syntax. *)
let int_litteral : (string * char option) Earley.grammar =
  let int_re =
    [ "[0][xX][0-9a-fA-F][0-9a-fA-F_]*" (* Hexadecimal            *)
    ; "[0][oO][0-7][0-7_]*"             (* Octal                  *)
    ; "[0][bB][01][01_]*"               (* Binary                 *)
    ; "[0-9][0-9_]*" ]                  (* Decimal (must be last) *)
  in
  parser i:RE(union_re int_re) num_suffix

(** [float_litteral] accepts a floating point litteral in any valid syntax. *)
let float_litteral : (string * char option) Earley.grammar =
  let float_re =
    [ "[0-9][0-9_]*[eE][+-]?[0-9][0-9_]*"
    ; "[0-9][0-9_]*[.][0-9_]*\\([eE][+-][0-9][0-9_]*\\)?" ]
  in
  parser f:RE(union_re float_re) num_suffix

(** {3 Character and string constants} *)

(** [escaped_char] accepts a single escaped character. *)
let escaped_char : char Earley.grammar =
  let char_dec = "[0-9][0-9][0-9]" in
  let char_hex = "[x][0-9a-fA-F][0-9a-fA-F]" in
  let char_esc = "[\\\\\\\"\\\'ntbrs ]" in
  parser
  | e:RE(char_dec) -> char_of_int (int_of_string e)
  | e:RE(char_hex) -> char_of_int (int_of_string ("0" ^ e))
  | e:RE(char_esc) -> match e.[0] with
                      | 'n' -> '\n' | 't' -> '\t' | 'b' -> '\b'
                      | 'r' -> '\r' | 's' -> ' '  | c   -> c

(** [char_litteral] accepts a single character litteral. *)
let char_litteral : char Earley.grammar =
  let char_reg = "[^\\\\\\\']" in
  let one_char =
    parser
    | c:RE(char_reg)      -> c.[0]
    | '\\' e:escaped_char -> e
  in
  Earley.no_blank_layout (parser _:single_quote c:one_char '\'')

(** [quoted_string] accepts a single quoted string ("{id|...|id}" syntax). *)
let quoted_string : (string * string option) Earley.grammar =
  let f buf pos =
    let rec fn st str buf pos =
      let (c, buf', pos') = Input.read buf pos in
      match (st, c) with
      | (`Ini          , '{'     ) -> fn (`Opn([])) str buf' pos'
      | (`Opn(l)       , 'a'..'z')
      | (`Opn(l)       , '_'     ) -> fn (`Opn(c::l)) str buf' pos'
      | (`Opn(l)       , '|'     ) -> fn (`Cnt(List.rev l)) str buf' pos'
      | (`Cnt(l)       , '|'     ) -> fn (`Cls(l,[],l)) str buf' pos'
      | (`Cnt(l)       , '\255'  ) -> Earley.give_up ()
      | (`Cnt(_)       , _       ) -> fn st (c::str) buf' pos'
      | (`Cls([]  ,_,l), '}'     ) -> (str, l, buf', pos') (* Success. *)
      | (`Cls([]  ,_,_), '\255'  ) -> Earley.give_up ()
      | (`Cls([]  ,b,l), _       ) -> fn (`Cnt(l)) (b @ str) buf' pos'
      | (`Cls(_::_,_,_), '\255'  ) -> Earley.give_up ()
      | (`Cls(x::y,b,l), _       ) ->
          if x = c then fn (`Cls(y,x::b,l)) str buf' pos'
          else fn (`Cnt(l)) (List.append b str) buf' pos'
      | (_             , _       ) -> Earley.give_up ()
    in
    let (cs, id, buf, pos) = fn `Ini [] buf pos in
    ((cs_to_string cs, Some (cs_to_string id)), buf, pos)
  in
  Earley.black_box f (Charset.singleton '{') false "quoted_string"

(** [normal_string] accepts a single standard string (with double quotes). *)
let normal_string : string Earley.grammar =
  let one_char =
    let char_reg = "[^\\\\\\\"]" in
    parser
    | c:RE(char_reg)      -> c.[0]
    | '\\' e:escaped_char -> e
  in
  parser '"' cs:one_char* css:{_:"\\\n" _:RE("[ \t]*")$ one_char*}* '"' ->
    cs_to_string (List.flatten (cs :: css))

(** [string_litteral] accepts a single string litteral. *)
let string_litteral : (string * string option) Earley.grammar =
  let string_litteral = parser s:normal_string -> (s, None) | quoted_string in
  Earley.no_blank_layout string_litteral

(** [regexp] accepts the contents of a regexp litteral (no delimitor). *)
let regexp : string Earley.grammar =
  let regexp_char = parser
    | c:RE("[^'\\\\]")            -> c
    | _:single_quote              -> "'"
    | '\\' e:RE("[ntbrs\\\\()|]") ->
        match e.[0] with
        | 'n'  -> "\n"  | 't'  -> "\t"  | 'b'  -> "\b"  | 'r'  -> "\r"
        | 's'  -> " "   | '\\' -> "\\"  | '('  -> "\\(" | ')'  -> "\\)"
        | '|'  -> "\\|" | _    -> assert false
  in
  parser cs:regexp_char* -> String.concat "" cs

(** [regexp_litteral] accepts a single Earley regexp litteral (with [Str]). *)
let regexp_litteral : string Earley.grammar =
  parser _:double_quote (Earley.no_blank_layout (parser regexp "''"))

(** [regexp_litteral] accepts a single Earley regexp litteral (builtin). *)
let new_regexp_litteral : string Earley.grammar =
  Earley.no_blank_layout (parser "{#" regexp "#}")
