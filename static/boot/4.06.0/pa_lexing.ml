open Earley_core
type buf_pos = (Input.buffer * int)
[@@@ocaml.text " Representation of a buffer with a specific position. "]
[@@@ocaml.text
  " {2 Comments and documentation comments} ********************************"]
exception Unclosed_comment of bool * Input.buffer * int 
[@@@ocaml.text
  " Exception [Unclosed_comment(in_str, buf, pos)] is raised when a comment at\n    is not closed properly at position [pos] in buffer [buf]. Note that if the\n    [in_str] is set to [true] then the problem is due to an unclosed string in\n    a comment. "]
let unclosed_comment : ?in_str:bool -> buf_pos -> 'a =
  fun ?(in_str= false) ->
    fun (buf, pos) -> raise (Unclosed_comment (in_str, buf, pos))
[@@@ocaml.text
  " [unclosed_comment ~in_str (buf, pos)] signals an unclodes comment. "]
type doc_comment = {
  doc_start: buf_pos ;
  doc_end: buf_pos ;
  doc_text: string }
[@@@ocaml.text " Representation of a documentation comment. "]
let doc_comments : doc_comment list ref = ref []
[@@@ocaml.text
  " [doc_comments] holds documentation comments that have already been parsed,\n    but only at the current level. "]
let doc_stack : doc_comment list list ref = ref []
[@@@ocaml.text
  " [doc_stack] is used to store documentation comment contexts that are in an\n    outer scope (e.g., a parrent module). "]
let push_comments : unit -> unit =
  fun _ -> doc_stack := ((!doc_comments) :: (!doc_stack)); doc_comments := []
[@@@ocaml.text
  " [push_comments ()] pushes the current documentation comments to the stack,\n    and reinitialises the current comments. This function is used whenever the\n    parser enters the scope of a new module/signature definition. "]
let pop_comments : unit -> unit =
  fun _ ->
    match !doc_stack with
    | [] -> assert false
    | c::stack -> (doc_comments := ((!doc_comments) @ c); doc_stack := stack)
[@@@ocaml.text
  " [pop_comments ()] pops back the documentation comments stored in the stack\n    (thus overwriting the currently stored documentation comments).  Note that\n    this function is used when getting out of a module definition. "]
let ocaml_blank : Earley.blank =
  fun buf ->
    fun pos ->
      let odoc = ref false in
      let odoc_buf = Buffer.create 1024 in
      let rec fn state stack prev ((buf, pos) as curr) =
        let (c, buf', pos') = Input.read buf pos in
        if !odoc then Buffer.add_char odoc_buf c;
        (let next = (buf', pos') in
         match (state, stack, c) with
         | (`Ini, [], ' ')|(`Ini, [], '\t')|(`Ini, [], '\r')|(`Ini, [], '\n')
             -> fn `Ini stack curr next
         | (`Ini, _, '(') -> fn (`Opn curr) stack curr next
         | (`Ini, [], _) -> curr
         | (`Opn p, [], '*') ->
             let (c1, buf', pos') = Input.read buf' pos' in
             let is_doc = (c1 = '*') && ((Input.get buf' pos') <> '*') in
             if is_doc
             then (odoc := true; fn `Cls [p] curr (buf', pos'))
             else fn `Ini [p] curr next
         | (`Opn p, _, '*') -> fn `Ini (p :: stack) curr next
         | (`Opn _, _::_, '"') -> fn (`Str curr) stack curr next
         | (`Opn _, _::_, '{') -> fn (`SOp ([], curr)) stack curr next
         | (`Opn _, _::_, '(') -> fn (`Opn curr) stack curr next
         | (`Opn _, [], _) -> prev
         | (`Opn _, _, _) -> fn `Ini stack curr next
         | (`Ini, _::_, '"') -> fn (`Str curr) stack curr next
         | (`Str _, _::_, '"') -> fn `Ini stack curr next
         | (`Str p, _::_, '\\') -> fn (`Esc p) stack curr next
         | (`Esc p, _::_, _) -> fn (`Str p) stack curr next
         | (`Str p, _::_, '\255') -> unclosed_comment ~in_str:true p
         | (`Str _, _::_, _) -> fn state stack curr next
         | (`Str _, [], _) -> assert false
         | (`Esc _, [], _) -> assert false
         | (`Ini, _::_, '{') -> fn (`SOp ([], curr)) stack curr next
         | (`SOp (l, p), _::_, 'a'..'z')|(`SOp (l, p), _::_, '_') ->
             fn (`SOp ((c :: l), p)) stack curr next
         | (`SOp (_, _), p::_, '\255') -> unclosed_comment p
         | (`SOp (l, p), _::_, '|') ->
             fn (`SIn ((List.rev l), p)) stack curr next
         | (`SOp (_, _), _::_, _) -> fn `Ini stack curr next
         | (`SIn (l, p), _::_, '|') -> fn (`SCl (l, (l, p))) stack curr next
         | (`SIn (_, p), _::_, '\255') -> unclosed_comment ~in_str:true p
         | (`SIn (_, _), _::_, _) -> fn state stack curr next
         | (`SCl ([], b), _::_, '}') -> fn `Ini stack curr next
         | (`SCl ([], b), _::_, '\255') ->
             unclosed_comment ~in_str:true (snd b)
         | (`SCl ([], b), _::_, _) -> fn (`SIn b) stack curr next
         | (`SCl (l, b), _::_, c) ->
             if c = (List.hd l)
             then fn (`SCl ((List.tl l), b)) stack curr next
             else fn (`SIn b) stack curr next
         | (`SOp (_, _), [], _) -> assert false
         | (`SIn (_, _), [], _) -> assert false
         | (`SCl (_, _), [], _) -> assert false
         | (`Ini, _::_, '*') -> fn `Cls stack curr next
         | (`Cls, _::_, '*') -> fn `Cls stack curr next
         | (`Cls, _::_, '"') -> fn (`Str curr) stack curr next
         | (`Cls, _::_, '{') -> fn (`SOp ([], curr)) stack curr next
         | (`Cls, p::s, ')') ->
             (if (!odoc) && (s = [])
              then
                (let text =
                   Buffer.sub odoc_buf 0 ((Buffer.length odoc_buf) - 2) in
                 Buffer.clear odoc_buf;
                 (let c = { doc_start = p; doc_end = next; doc_text = text } in
                  doc_comments := (c :: (!doc_comments)); odoc := false));
              fn `Ini s curr next)
         | (`Cls, _::_, _) -> fn `Ini stack curr next
         | (`Cls, [], _) -> assert false
         | (`Ini, p::_, '\255') -> unclosed_comment p
         | (`Ini, _::_, _) -> fn `Ini stack curr next) in
      fn `Ini [] (buf, pos) (buf, pos)
[@@@ocaml.text
  " [ocaml_blank buf pos] is the Earley blank function for OCaml, that ignores\n    blanks starting at buffer [buf] and position [pos]. The ignored characters\n    include [' '], ['\\t'], ['\\r'], ['\\n'], everything enclosed between  [\"(*\"]\n    and [\"*)\"] (multi-line comments). Multi-line comments can contain (nested)\n    multi-line comments,  as well as valid string litterals (including strings\n    such as [\"(*\"] or [\"*)\"]). "]
[@@@ocaml.text
  " {2 Keywords management} ************************************************"]
let is_identifier_char : char -> bool =
  fun c ->
    match c with | 'a'..'z'|'A'..'Z'|'0'..'9'|'_'|'\'' -> true | _ -> false
[@@@ocaml.text
  " [is_identifier_char c] tells whether [c] could appear in an identifier. "]
let key_word s =
  if (String.length s) <= 0 then invalid_arg "Pa_lexing.key_word";
  Earley.keyword s is_identifier_char ()
[@@@ocaml.text " [keyword s] creates a keyword parser for [s]. "]
[@@@ocaml.text " {3 Keyword declarations} "]
let mutable_kw = key_word "mutable"
let private_kw = key_word "private"
let virtual_kw = key_word "virtual"
let rec_kw = key_word "rec"
let to_kw = key_word "to"
let downto_kw = key_word "downto"
let joker_kw = key_word "_"
let method_kw = key_word "method"
let object_kw = key_word "object"
let class_kw = key_word "class"
let inherit_kw = key_word "inherit"
let as_kw = key_word "as"
let of_kw = key_word "of"
let module_kw = key_word "module"
let open_kw = key_word "open"
let include_kw = key_word "include"
let type_kw = key_word "type"
let val_kw = key_word "val"
let external_kw = key_word "external"
let constraint_kw = key_word "constraint"
let begin_kw = key_word "begin"
let end_kw = key_word "end"
let and_kw = key_word "and"
let true_kw = key_word "true"
let false_kw = key_word "false"
let exception_kw = key_word "exception"
let when_kw = key_word "when"
let fun_kw = key_word "fun"
let function_kw = key_word "function"
let let_kw = key_word "let"
let in_kw = key_word "in"
let initializer_kw = key_word "initializer"
let with_kw = key_word "with"
let while_kw = key_word "while"
let for_kw = key_word "for"
let do_kw = key_word "do"
let done_kw = key_word "done"
let new_kw = key_word "new"
let assert_kw = key_word "assert"
let if_kw = key_word "if"
let then_kw = key_word "then"
let else_kw = key_word "else"
let try_kw = key_word "try"
let match_kw = key_word "match"
let struct_kw = key_word "struct"
let functor_kw = key_word "functor"
let sig_kw = key_word "sig"
let lazy_kw = key_word "lazy"
let parser_kw = key_word "parser"
let cached_kw = key_word "cached"
let mutable_flag = Earley_core.Earley.declare_grammar "mutable_flag"
let _ =
  Earley_core.Earley.set_grammar mutable_flag
    (Earley_core.Earley.alternatives
       [Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
          (Earley_core.Earley.empty Asttypes.Immutable);
       Earley_core.Earley.fsequence mutable_kw
         (Earley_core.Earley.empty (fun _default_0 -> Asttypes.Mutable))] : 
    Asttypes.mutable_flag Earley.grammar)
[@@@ocaml.text
  " [mutable_flag] is a parser for an optional \"mutable\" keyword. "]
let private_flag = Earley_core.Earley.declare_grammar "private_flag"
let _ =
  Earley_core.Earley.set_grammar private_flag
    (Earley_core.Earley.alternatives
       [Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
          (Earley_core.Earley.empty Asttypes.Public);
       Earley_core.Earley.fsequence private_kw
         (Earley_core.Earley.empty (fun _default_0 -> Asttypes.Private))] : 
    Asttypes.private_flag Earley.grammar)
[@@@ocaml.text
  " [private_flag] is a parser for an optional \"private\" keyword. "]
let virtual_flag = Earley_core.Earley.declare_grammar "virtual_flag"
let _ =
  Earley_core.Earley.set_grammar virtual_flag
    (Earley_core.Earley.alternatives
       [Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
          (Earley_core.Earley.empty Asttypes.Concrete);
       Earley_core.Earley.fsequence virtual_kw
         (Earley_core.Earley.empty (fun _default_0 -> Asttypes.Virtual))] : 
    Asttypes.virtual_flag Earley.grammar)
[@@@ocaml.text
  " [virtual_flag] is a parser for an optional \"virtual\" keyword. "]
let rec_flag = Earley_core.Earley.declare_grammar "rec_flag"
let _ =
  Earley_core.Earley.set_grammar rec_flag
    (Earley_core.Earley.alternatives
       [Earley_core.Earley.fsequence_ignore (Earley_core.Earley.empty ())
          (Earley_core.Earley.empty Asttypes.Nonrecursive);
       Earley_core.Earley.fsequence rec_kw
         (Earley_core.Earley.empty (fun _default_0 -> Asttypes.Recursive))] : 
    Asttypes.rec_flag Earley.grammar)
[@@@ocaml.text " [rec_flag] is a parser for an optional \"rec\" keyword. "]
let downto_flag = Earley_core.Earley.declare_grammar "downto_flag"
let _ =
  Earley_core.Earley.set_grammar downto_flag
    (Earley_core.Earley.alternatives
       [Earley_core.Earley.fsequence downto_kw
          (Earley_core.Earley.empty (fun _default_0 -> Asttypes.Downto));
       Earley_core.Earley.fsequence to_kw
         (Earley_core.Earley.empty (fun _default_0 -> Asttypes.Upto))] : 
    Asttypes.direction_flag Earley.grammar)
[@@@ocaml.text
  " [downto_flag] is a parser for either a \"to\" or a \"downto\" keyword. "]
[@@@ocaml.text " {3 Some parsers to forbid keywords} "]
let no_keyword : string -> unit Earley.grammar =
  fun s ->
    let len = String.length s in
    let rec fn i buf pos =
      let (c, buf, pos) = Input.read buf pos in
      if i >= len
      then ((), (is_identifier_char c))
      else if c <> (s.[i]) then ((), true) else fn (i + 1) buf pos in
    Earley.test ~name:("no_" ^ s) Charset.full (fn 0)
[@@@ocaml.text
  " [not_keyword s] fails if the input matches keyword [s], and does not parse\n    any input (i.e., this is only a test combinator). "]
let no_else = no_keyword "else"
let no_with = no_keyword "with"
let no_parser = no_keyword "parser"
[@@@ocaml.text " {3 Other similar functions for reserved sequences} "]
let no_dot : unit Earley.grammar =
  let fn buf pos = ((), ((Input.get buf pos) <> '.')) in
  Earley.test ~name:"no_dot" Charset.full fn
[@@@ocaml.text
  " [no_dot] is a grammar that fails if the next character is ['.']. Note that\n    not input is consumed, whatever the outcome of the test. "]
let no_semi : unit Earley.grammar =
  let fn buf pos =
    let (c, buf, pos) = Input.read buf pos in
    ((), ((c <> ';') || ((Input.get buf pos) = ';'))) in
  Earley.test ~name:"no_semi" Charset.full fn
[@@@ocaml.text
  " [no_semi] is a grammar that fails if the next character is a [';'], except\n    if the second next character is also [';']. No input is consumed. "]
let no_colon : unit Earley.grammar =
  let fn buf pos =
    let (c, buf, pos) = Input.read buf pos in
    ((), ((c <> ':') || ((Input.get buf pos) = ':'))) in
  Earley.test ~name:"no_colon" Charset.full fn
[@@@ocaml.text
  " [no_semi] is a grammar that fails if the next character is a [':'], except\n    if the second next character is also [':']. No input is consumed. "]
[@@@ocaml.text
  " {2 Identifiers} ********************************************************"]
let make_reserved : string list -> ((string -> bool) * (string -> unit)) =
  fun l ->
    let htbl = Hashtbl.create 37 in
    List.iter (fun s -> Hashtbl.add htbl s s) l;
    ((Hashtbl.mem htbl), ((fun s -> Hashtbl.add htbl s s)))
[@@@ocaml.text
  " [make_reserved l] initializes a structure for storing a list of (reserved)\n    strings to [l], and returns a pair of functions [(mem, add)], respectively\n    testing the membership of a string and adding a new reserved element. "]
let (is_reserved_id, add_reserved_id) =
  make_reserved
    ["and";
    "as";
    "assert";
    "asr";
    "begin";
    "class";
    "constraint";
    "do";
    "done";
    "downto";
    "else";
    "end";
    "exception";
    "external";
    "false";
    "for";
    "function";
    "functor";
    "fun";
    "if";
    "in";
    "include";
    "inherit";
    "initializer";
    "land";
    "lazy";
    "let";
    "lor";
    "lsl";
    "lsr";
    "lxor";
    "match";
    "method";
    "mod";
    "module";
    "mutable";
    "new";
    "object";
    "of";
    "open";
    "or";
    "private";
    "rec";
    "sig";
    "struct";
    "then";
    "to";
    "true";
    "try";
    "type";
    "val";
    "virtual";
    "when";
    "while";
    "with";
    "_"]
[@@@ocaml.text
  " Functions for manipulating reserved identifiers (e.g., keywords). "]
let (is_reserved_symb, add_reserved_symb) =
  make_reserved
    ["#";
    "'";
    "(";
    ")";
    ",";
    "->";
    "->>";
    ".";
    "..";
    ":";
    ":>";
    ";";
    ";;";
    "<-";
    ">]";
    ">}";
    "?";
    "[";
    "[<";
    "[>";
    "[|";
    "]";
    "_";
    "`";
    "{";
    "{<";
    "|";
    "|]";
    "}";
    "~";
    "$"]
[@@@ocaml.text " Functions for manipulating reserved symbols. "]
let ident = Earley_core.Earley.declare_grammar "ident"
let _ =
  Earley_core.Earley.set_grammar ident
    (Earley_core.Earley.fsequence
       (Earley_str.regexp ~name:"[A-Za-z_][a-zA-Z0-9_']*"
          "[A-Za-z_][a-zA-Z0-9_']*" (fun groupe -> groupe 0))
       (Earley_core.Earley.empty
          (fun id -> if is_reserved_id id then Earley.give_up (); id)))
[@@@ocaml.text
  " [ident] is a grammar that accepts any lowercase or upercase identifier, as\n    long as it is not reserved according to the [is_reserved_id] function. "]
let lident = Earley_core.Earley.declare_grammar "lident"
let _ =
  Earley_core.Earley.set_grammar lident
    (Earley_core.Earley.fsequence
       (Earley_str.regexp ~name:"[a-z_][a-zA-Z0-9_']*" "[a-z_][a-zA-Z0-9_']*"
          (fun groupe -> groupe 0))
       (Earley_core.Earley.empty
          (fun id -> if is_reserved_id id then Earley.give_up (); id)))
[@@@ocaml.text
  " [lident] is a grammar that accepts any non-reserved, lowercase identifier.\n    Reserved identifiers are identified using [is_reserved_id]. "]
let uident = Earley_core.Earley.declare_grammar "uident"
let _ =
  Earley_core.Earley.set_grammar uident
    (Earley_str.regexp ~name:"[A-Z][a-zA-Z0-9_']*" "[A-Z][a-zA-Z0-9_']*"
       (fun groupe -> groupe 0))
[@@@ocaml.text
  " [uident] is a grammar that accepts any uppercase identifier. "]
[@@@ocaml.text " {3 Special characters and delimiters} "]
let not_special : unit Earley.grammar =
  let cs = ref Charset.empty in
  String.iter (fun c -> cs := (Charset.add (!cs) c)) "!$%&*+./:<=>?@^|~-";
  Earley.blank_not_in_charset ~name:"not_special" (!cs)
[@@@ocaml.text
  " [not_special] can be used to reject the current input if it is immediately\n    followed by a special (infix or prefix operator) character. In the process\n    no blank characters are ignored prior to testing. "]
let single_char : char -> unit Earley.grammar =
  fun c ->
    let fn str pos =
      let (c_read, str, pos) = Input.read str pos in
      if (c <> c_read) || ((Input.get str pos) = c) then Earley.give_up ();
      ((), str, pos) in
    Earley.black_box fn (Charset.singleton c) false (String.make 1 c)
[@@@ocaml.text
  " [single_char c] is a grammar that accepts a single [c] character, but that\n    rejects the input if it is then again followed by [c]. "]
let double_char : char -> unit Earley.grammar =
  fun c ->
    let fn str pos =
      let (c_read, str, pos) = Input.read str pos in
      if c_read <> c then Earley.give_up ();
      (let (c_read, str, pos) = Input.read str pos in
       if (c_read <> c) || ((Input.get str pos) = c) then Earley.give_up ();
       ((), str, pos)) in
    Earley.black_box fn (Charset.singleton c) false (String.make 2 c)
[@@@ocaml.text
  " [double_char c] is a grammar that accepts a sequence of (exactly) two [c].\n    If a third [c] follows, the input is rejected. "]
let semi_col = single_char ';'
let double_semi_col = double_char ';'
let single_quote = single_char '\''
let double_quote = double_char '\''
[@@@ocaml.text
  " {2 Constants and litterals} ********************************************"]
let union_re : string list -> string =
  fun l -> String.concat "\\|" (List.map (Printf.sprintf "\\(%s\\)") l)
[@@@ocaml.text
  " [union_re l] builds the string representation (following [Str] syntax]) of\n    a regular expression that is the alternative of the regular expressions in\n    the list [l]. "]
let cs_to_string : char list -> string =
  let b = Buffer.create 27 in
  fun cs -> let open Buffer in clear b; List.iter (add_char b) cs; contents b
[@@@ocaml.text
  " [cs_to_string cs] converts a list of characters into a string. "]
let bool_lit = Earley_core.Earley.declare_grammar "bool_lit"
let _ =
  Earley_core.Earley.set_grammar bool_lit
    (Earley_core.Earley.alternatives
       [Earley_core.Earley.fsequence true_kw
          (Earley_core.Earley.empty (fun _default_0 -> "true"));
       Earley_core.Earley.fsequence false_kw
         (Earley_core.Earley.empty (fun _default_0 -> "false"))] : string
                                                                    Earley.grammar)
[@@@ocaml.text " [bool_lit] accepts a single boolean litteral. "]
[@@@ocaml.text " {3 Numerical constants} "]
let num_suffix : char option Earley.grammar =
  let suffix_cs = let open Charset in union (range 'g' 'z') (range 'G' 'Z') in
  let no_suffix_cs = List.fold_left Charset.add suffix_cs ['.'; 'e'; 'E'] in
  let no_suffix buf pos _ _ =
    ((), (not (Charset.mem no_suffix_cs (Input.get buf pos)))) in
  Earley_core.Earley.alternatives
    [Earley_core.Earley.fsequence_ignore
       (Earley.blank_test Charset.full no_suffix)
       (Earley_core.Earley.empty None);
    Earley_core.Earley.fsequence_ignore (Earley_core.Earley.no_blank_test ())
      (Earley_core.Earley.fsequence (Earley.in_charset suffix_cs)
         (Earley_core.Earley.empty (fun s -> Some s)))]
[@@@ocaml.text
  " [num_suffix] accepts an optional numerical suffix character. "]
let int_litteral : (string * char option) Earley.grammar =
  let int_re =
    ["[0][xX][0-9a-fA-F][0-9a-fA-F_]*";
    "[0][oO][0-7][0-7_]*";
    "[0][bB][01][01_]*";
    "[0-9][0-9_]*"] in
  Earley_core.Earley.fsequence
    (Earley_str.regexp (union_re int_re) (fun groupe -> groupe 0))
    (Earley_core.Earley.fsequence num_suffix
       (Earley_core.Earley.empty (fun _default_0 -> fun i -> (i, _default_0))))
[@@@ocaml.text
  " [int_litteral] accepts an integer litteral in any valid syntax. "]
let float_litteral : (string * char option) Earley.grammar =
  let float_re =
    ["[0-9][0-9_]*[eE][+-]?[0-9][0-9_]*";
    "[0-9][0-9_]*[.][0-9_]*\\([eE][+-][0-9][0-9_]*\\)?"] in
  Earley_core.Earley.fsequence
    (Earley_str.regexp (union_re float_re) (fun groupe -> groupe 0))
    (Earley_core.Earley.fsequence num_suffix
       (Earley_core.Earley.empty (fun _default_0 -> fun f -> (f, _default_0))))
[@@@ocaml.text
  " [float_litteral] accepts a floating point litteral in any valid syntax. "]
[@@@ocaml.text " {3 Character and string constants} "]
let escaped_char : char Earley.grammar =
  let char_dec = "[0-9][0-9][0-9]" in
  let char_hex = "[x][0-9a-fA-F][0-9a-fA-F]" in
  let char_esc = "[\\\\\\\"\\'ntbrs ]" in
  Earley_core.Earley.alternatives
    [Earley_core.Earley.fsequence
       (Earley_str.regexp ~name:"char_esc" char_esc (fun groupe -> groupe 0))
       (Earley_core.Earley.empty
          (fun e ->
             match e.[0] with
             | 'n' -> '\n'
             | 't' -> '\t'
             | 'b' -> '\b'
             | 'r' -> '\r'
             | 's' -> ' '
             | c -> c));
    Earley_core.Earley.fsequence
      (Earley_str.regexp ~name:"char_dec" char_dec (fun groupe -> groupe 0))
      (Earley_core.Earley.empty (fun e -> char_of_int (int_of_string e)));
    Earley_core.Earley.fsequence
      (Earley_str.regexp ~name:"char_hex" char_hex (fun groupe -> groupe 0))
      (Earley_core.Earley.empty
         (fun e -> char_of_int (int_of_string ("0" ^ e))))]
[@@@ocaml.text " [escaped_char] accepts a single escaped character. "]
let char_litteral : char Earley.grammar =
  let char_reg = "[^\\\\\\']" in
  let one_char =
    Earley_core.Earley.alternatives
      [Earley_core.Earley.fsequence_ignore
         (Earley_core.Earley.char '\\' '\\')
         (Earley_core.Earley.fsequence escaped_char
            (Earley_core.Earley.empty (fun e -> e)));
      Earley_core.Earley.fsequence
        (Earley_str.regexp ~name:"char_reg" char_reg (fun groupe -> groupe 0))
        (Earley_core.Earley.empty (fun c -> c.[0]))] in
  Earley.no_blank_layout
    (Earley_core.Earley.fsequence_ignore single_quote
       (Earley_core.Earley.fsequence one_char
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '\'' '\'')
             (Earley_core.Earley.empty (fun c -> c)))))
[@@@ocaml.text " [char_litteral] accepts a single character litteral. "]
let quoted_string : (string * string option) Earley.grammar =
  let f buf pos =
    let rec fn st str buf pos =
      let (c, buf', pos') = Input.read buf pos in
      match (st, c) with
      | (`Ini, '{') -> fn (`Opn []) str buf' pos'
      | (`Opn l, 'a'..'z')|(`Opn l, '_') -> fn (`Opn (c :: l)) str buf' pos'
      | (`Opn l, '|') -> fn (`Cnt (List.rev l)) str buf' pos'
      | (`Cnt l, '|') -> fn (`Cls (l, [], l)) str buf' pos'
      | (`Cnt l, '\255') -> Earley.give_up ()
      | (`Cnt _, _) -> fn st (c :: str) buf' pos'
      | (`Cls ([], _, l), '}') -> (str, l, buf', pos')
      | (`Cls ([], _, _), '\255') -> Earley.give_up ()
      | (`Cls ([], b, l), _) -> fn (`Cnt l) (b @ str) buf' pos'
      | (`Cls (_::_, _, _), '\255') -> Earley.give_up ()
      | (`Cls (x::y, b, l), _) ->
          if x = c
          then fn (`Cls (y, (x :: b), l)) str buf' pos'
          else fn (`Cnt l) (List.append b str) buf' pos'
      | (_, _) -> Earley.give_up () in
    let (cs, id, buf, pos) = fn `Ini [] buf pos in
    (((cs_to_string cs), (Some (cs_to_string id))), buf, pos) in
  Earley.black_box f (Charset.singleton '{') false "quoted_string"
[@@@ocaml.text
  " [quoted_string] accepts a single quoted string (\"{id|...|id}\" syntax). "]
let normal_string : string Earley.grammar =
  let one_char =
    let char_reg = "[^\\\\\\\"]" in
    Earley_core.Earley.alternatives
      [Earley_core.Earley.fsequence_ignore
         (Earley_core.Earley.char '\\' '\\')
         (Earley_core.Earley.fsequence escaped_char
            (Earley_core.Earley.empty (fun e -> e)));
      Earley_core.Earley.fsequence
        (Earley_str.regexp ~name:"char_reg" char_reg (fun groupe -> groupe 0))
        (Earley_core.Earley.empty (fun c -> c.[0]))] in
  Earley_core.Earley.fsequence_ignore (Earley_core.Earley.char '"' '"')
    (Earley_core.Earley.fsequence
       (Earley_core.Earley.apply (fun f -> f [])
          (Earley_core.Earley.fixpoint' (fun l -> l) one_char
             (fun x -> fun f -> fun l -> f (x :: l))))
       (Earley_core.Earley.fsequence
          (Earley_core.Earley.apply (fun f -> f [])
             (Earley_core.Earley.fixpoint' (fun l -> l)
                (Earley_core.Earley.fsequence_ignore
                   (Earley_core.Earley.string "\\\n" "\\\n")
                   (Earley_core.Earley.fsequence_ignore
                      (Earley_core.Earley.greedy
                         (Earley_str.regexp "[ \t]*" (fun groupe -> groupe 0)))
                      (Earley_core.Earley.fsequence
                         (Earley_core.Earley.apply (fun f -> f [])
                            (Earley_core.Earley.fixpoint' (fun l -> l)
                               one_char
                               (fun x -> fun f -> fun l -> f (x :: l))))
                         (Earley_core.Earley.empty
                            (fun _default_0 -> _default_0)))))
                (fun x -> fun f -> fun l -> f (x :: l))))
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.char '"' '"')
             (Earley_core.Earley.empty
                (fun css -> fun cs -> cs_to_string (List.flatten (cs :: css)))))))
[@@@ocaml.text
  " [normal_string] accepts a single standard string (with double quotes). "]
let string_litteral : (string * string option) Earley.grammar =
  let string_litteral =
    Earley_core.Earley.alternatives
      [quoted_string;
      Earley_core.Earley.fsequence normal_string
        (Earley_core.Earley.empty (fun s -> (s, None)))] in
  Earley.no_blank_layout string_litteral
[@@@ocaml.text " [string_litteral] accepts a single string litteral. "]
let regexp : string Earley.grammar =
  let regexp_char =
    Earley_core.Earley.alternatives
      [Earley_core.Earley.fsequence_ignore
         (Earley_core.Earley.char '\\' '\\')
         (Earley_core.Earley.fsequence
            (Earley_str.regexp "[ntbrs\\\\()|]" (fun groupe -> groupe 0))
            (Earley_core.Earley.empty
               (fun e ->
                  match e.[0] with
                  | 'n' -> "\n"
                  | 't' -> "\t"
                  | 'b' -> "\b"
                  | 'r' -> "\r"
                  | 's' -> " "
                  | '\\' -> "\\"
                  | '(' -> "\\("
                  | ')' -> "\\)"
                  | '|' -> "\\|"
                  | _ -> assert false)));
      Earley_str.regexp "[^'\\\\]" (fun groupe -> groupe 0);
      Earley_core.Earley.fsequence_ignore single_quote
        (Earley_core.Earley.empty "'")] in
  Earley_core.Earley.fsequence
    (Earley_core.Earley.apply (fun f -> f [])
       (Earley_core.Earley.fixpoint' (fun l -> l) regexp_char
          (fun x -> fun f -> fun l -> f (x :: l))))
    (Earley_core.Earley.empty (fun cs -> String.concat "" cs))
[@@@ocaml.text
  " [regexp] accepts the contents of a regexp litteral (no delimitor). "]
let regexp_litteral : string Earley.grammar =
  Earley_core.Earley.fsequence_ignore double_quote
    (Earley_core.Earley.fsequence
       (Earley.no_blank_layout
          (Earley_core.Earley.fsequence regexp
             (Earley_core.Earley.fsequence_ignore
                (Earley_core.Earley.string "''" "''")
                (Earley_core.Earley.empty (fun _default_0 -> _default_0)))))
       (Earley_core.Earley.empty (fun _default_0 -> _default_0)))
[@@@ocaml.text
  " [regexp_litteral] accepts a single Earley regexp litteral (with [Str]). "]
let new_regexp_litteral : string Earley.grammar =
  Earley.no_blank_layout
    (Earley_core.Earley.fsequence_ignore
       (Earley_core.Earley.string "{#" "{#")
       (Earley_core.Earley.fsequence regexp
          (Earley_core.Earley.fsequence_ignore
             (Earley_core.Earley.string "#}" "#}")
             (Earley_core.Earley.empty (fun _default_0 -> _default_0)))))
