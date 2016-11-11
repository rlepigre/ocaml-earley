(*
  ======================================================================
  Copyright Christophe Raffalli & Rodolphe Lepigre
  LAMA, UMR 5127 - Université Savoie Mont Blanc

  christophe.raffalli@univ-savoie.fr
  rodolphe.lepigre@univ-savoie.fr

  This software contains implements a parser combinator library together
  with a syntax extension mechanism for the OCaml language.  It  can  be
  used to write parsers using a BNF-like format through a syntax extens-
  ion called pa_parser.

  This software is governed by the CeCILL-B license under French law and
  abiding by the rules of distribution of free software.  You  can  use,
  modify and/or redistribute it under the terms of the CeCILL-B  license
  as circulated by CEA, CNRS and INRIA at the following URL:

            http://www.cecill.info

  The exercising of this freedom is conditional upon a strong obligation
  of giving credits for everybody that distributes a software incorpora-
  ting a software ruled by the current license so as  all  contributions
  to be properly identified and acknowledged.

  As a counterpart to the access to the source code and rights to  copy,
  modify and redistribute granted by the  license,  users  are  provided
  only with a limited warranty and the software's author, the holder  of
  the economic rights, and the successive licensors  have  only  limited
  liability.

  In this respect, the user's attention is drawn to the risks associated
  with loading, using, modifying and/or developing  or  reproducing  the
  software by the user in light of its specific status of free software,
  that may mean that it is complicated  to  manipulate,  and  that  also
  therefore means that it is reserved  for  developers  and  experienced
  professionals having in-depth computer knowledge. Users are  therefore
  encouraged to load and test  the  software's  suitability  as  regards
  their requirements in conditions enabling the security of  their  sys-
  tems and/or data to be ensured and, more generally, to use and operate
  it in the same conditions as regards security.

  The fact that you are presently reading this means that you  have  had
  knowledge of the CeCILL-B license and that you accept its terms.
  ======================================================================
*)

type line =
  { is_eof       : bool   (* Has the end of the buffer been reached? *)
  ; lnum         : int    (* Line number (startig at 1)              *)
  ; loff         : int    (* Offset to the line                      *)
  ; llen         : int    (* Length of the line                      *)
  ; data         : string (* Contents of the line                    *)
  ; mutable next : buffer (* Following line                          *)
  ; name         : string (* The name of the buffer (e.g. file name) *)
  ; uid          : int }  (* Unique identifier                       *)

and buffer = line Lazy.t

(* Generate a unique identifier. *)
let new_uid =
  let c = ref 0 in
  fun () -> let uid = !c in incr c; uid

(* Emtpy buffer. *)
let empty_buffer name lnum loff =
  let rec line = lazy
    { is_eof = true ; name ; lnum ; loff ; llen = 0
    ; data = "" ; next = line ; uid = new_uid () }
  in line

(* Test if a buffer is empty. *)
let rec is_empty (lazy l) pos =
  if pos < l.llen then false
  else if pos = 0 then l.is_eof
  else is_empty l.next (pos - l.llen)

(* Read the character at the given position in the given buffer. *)
let rec read (lazy l as b) i =
  if l.is_eof then ('\255', b, 0) else
  match compare (i+1) l.llen with
  | -1 -> (l.data.[i], b     , i+1)
  | 0  -> (l.data.[i], l.next, 0  )
  | _  -> read l.next (i - l.llen)

(* Get the character at the given position in the given buffer. *)
let rec get (lazy l) i =
  if l.is_eof then '\255' else
  if i < l.llen then l.data.[i]
  else get l.next (i - l.llen)

(* Get the name of a buffer. *)
let fname (lazy b) = b.name

(* Get the current line number of a buffer. *)
let line_num (lazy b) = b.lnum

(* Get the offset of the current line in the full buffer. *)
let line_beginning (lazy b) = b.loff

(* Get the current line as a string. *)
let line (lazy b) = b.data

(* Get the length of the current line. *)
let line_length (lazy b) = b.llen

(* Get the utf8 column number corresponding to the given position. *)
let utf8_col_num (lazy {data}) i =
  let rec find num pos =
    if pos < i then
      let cc = Char.code data.[pos] in
      if cc lsr 7 = 0 then find (num+1) (pos+1) else
      if (cc lsr 6) land 1 = 0 then -1 else (* Invalid utf8 character *)
      if (cc lsr 5) land 1 = 0 then find (num+1) (pos+2) else
      if (cc lsr 4) land 1 = 0 then find (num+1) (pos+3) else
      if (cc lsr 3) land 1 = 0 then find (num+1) (pos+4) else
      -0 (* Invalid utf8 character. *)
    else num
  in find 0 0

let rec normalize (lazy b as str) pos =
  if pos >= b.llen then
    if b.is_eof then str, 0 else normalize b.next (pos - b.llen)
  else str, pos

let lexing_position str pos =
  let loff = line_beginning str in
  Lexing.({ pos_fname = fname str
          ; pos_lnum  = line_num str
          ; pos_cnum  = loff +pos
          ; pos_bol   = loff })

module Regexp =
  struct
    (** A small module for efficient regular expressions. *)

    (** Type of a regular expression. *)
    type regexp =
      | Chr of char                (** Single character.              *)
      | Set of Charset.t           (** Any character in a charset.    *)
      | Seq of regexp list         (** Sequence of regexps.           *)
      | Alt of regexp list         (** Alternative between regexps.   *)
      | Opt of regexp              (** Optional regexp.               *)
      | Str of regexp              (** Zero or more times the regexp. *)
      | Pls of regexp              (** One  or more times the regexp. *)
      | Sav of regexp * string ref (** Save what is read.             *)

    (** [print_regexp ch re] prints the regexp [re] on the channel [ch]. *)
    let print_regexp ch re =
      let rec pregexp ch = function
        | Chr(c)   -> Printf.fprintf ch "Chr(%C)" c
        | Set(s)   -> Printf.fprintf ch "Set(%a)" Charset.print_charset s
        | Seq(l)   -> Printf.fprintf ch "Seq([%a])" pregexps l
        | Alt(l)   -> Printf.fprintf ch "Alt([%a])" pregexps l
        | Opt(r)   -> Printf.fprintf ch "Opt(%a)" pregexp r
        | Str(r)   -> Printf.fprintf ch "Str(%a)" pregexp r
        | Pls(r)   -> Printf.fprintf ch "Pls(%a)" pregexp r
        | Sav(r,_) -> Printf.fprintf ch "Sav(%a,<ref>)" pregexp r
      and pregexps ch = function
        | [] -> ()
        | [x] -> pregexp ch x
        | x::l -> Printf.fprintf ch "%a;%a" pregexp x pregexps l
      in
      pregexp ch re

    type construction =
        Acc of regexp list
      | Par of regexp list * regexp list

    let push x = function
      | Acc l -> Acc (x::l)
      | Par (l1, l2) -> Acc(Alt(x :: l1)::l2)

    let push_alt x = function
      | Acc(Seq l1 :: l2) -> Par(l1,l2)
      | Acc(x :: l2) -> Par([x], l2)
      | Acc([]) -> assert false
      | Par(_) -> assert false

    let pop = function
      | Acc l -> l
      | Par _ -> invalid_arg "Regexp: final bar."

    let regexp_from_string : string -> regexp * string ref array = fun s ->
      let cs =
        let cs = ref [] in
        for i = String.length s - 1 downto 0 do
          cs := s.[i] :: !cs
        done; !cs
      in

      let read_range cs =
        let rec read_range acc = function
          | []              -> invalid_arg "Regexp: open charset."
          | ']'::cs         -> (acc, cs)
          | c1::'-'::c2::cs -> let r = Charset.range c1 c2 in
                               read_range (Charset.union acc r) cs
          | c::cs           -> read_range (Charset.add acc c) cs
        in read_range Charset.empty cs
      in
      let rec tokens cs =
        let is_spe c = List.mem c ['\\';'.';'*';'+';'?';'[';']'] in
        match cs with
        | '.' ::cs            -> `Set(Charset.full) :: tokens cs
        | '*' ::cs            -> `Str :: tokens cs
        | '+' ::cs            -> `Pls :: tokens cs
        | '?' ::cs            -> `Opt :: tokens cs
        | '\\'::'('::cs       -> `Opn :: tokens cs
        | '\\'::')'::cs       -> `Cls :: tokens cs
        | '\\'::'|'::cs       -> `Alt :: tokens cs
        | '\\'::c  ::cs       -> if is_spe c then `Chr(c) :: tokens cs
                                 else invalid_arg "Regexp: invalid escape."
        | '\\'::[]            -> invalid_arg "Regexp: nothing to escape."
        | '[' ::'^':: ']'::cs -> let (rng, cs) = read_range cs in
                                 let rng = Charset.add rng ']' in
                                 `Set(Charset.complement rng) :: tokens cs
        | '[' ::']':: cs      -> let (rng, cs) = read_range cs in
                                 `Set(Charset.add rng ']') :: tokens cs
        | '[' ::'^'::cs       -> let (rng, cs) = read_range cs in
                                 `Set(Charset.complement rng) :: tokens cs
        | '[' ::cs            -> let (rng, cs) = read_range cs in
                                 `Set(rng) :: tokens cs
        | c   ::cs            -> `Chr(c) :: tokens cs
        | []                  -> []
      in
      let ts = tokens cs in

      let refs = ref [] in
      let rec build_re stk acc ts =
        match (stk, acc, ts) with
        | (stk   , acc    , `Chr(c)::ts) -> build_re stk (push (Chr c) acc) ts
        | (stk   , acc    , `Set(s)::ts) -> build_re stk (push (Set s) acc) ts
        | (stk   , Acc(Alt (re::l)::acc), `Str   ::ts) -> build_re stk (Acc(Alt(Str re::l) :: acc)) ts
        | (stk   , Acc(Alt (re::l)::acc), `Pls   ::ts) -> build_re stk (Acc(Alt(Pls re::l) :: acc)) ts
        | (stk   , Acc(Alt (re::l)::acc), `Opt   ::ts) -> build_re stk (Acc(Alt(Opt re::l) :: acc)) ts
        | (stk   , Acc(re::acc), `Str   ::ts) -> build_re stk (Acc(Str re :: acc)) ts
        | (stk   , Acc(re::acc), `Pls   ::ts) -> build_re stk (Acc(Pls re :: acc)) ts
        | (stk   , Acc(re::acc), `Opt   ::ts) -> build_re stk (Acc(Opt re :: acc)) ts
        | (stk   , _     , `Str   ::_ )
        | (stk   , _     , `Pls   ::_ )
        | (stk   , _     , `Opt   ::_ ) ->
            invalid_arg "Regexp: modifier error."
        | (stk   , acc    , `Opn   ::ts) -> build_re (pop acc::stk) (Acc []) ts
        | ([]    , _      , `Cls   ::_ ) ->
            invalid_arg "Regexp: group not opened."
        | (s::stk, acc    , `Cls   ::ts) ->
            let re =
              match List.rev (pop acc) with
              | [re] -> re
              | l    -> Seq(l)
            in
            let r = ref "" in refs := r :: !refs;
            build_re stk (Acc(Sav(re,r)::s)) ts
        | (stk   , Acc(re::acc), `Alt   ::ts) -> build_re stk (Par([re],acc)) ts
        | (stk   , Acc []      , `Alt   ::ts) -> invalid_arg "Regexp: initial bar."
        | (stk   , Par _       , `Alt   ::ts) -> invalid_arg "Regexp: consecutive bar."
        | ([]    , acc    , []         ) ->
            begin
              match List.rev (pop acc) with
              | [re] -> re
              | l    -> Seq(l)
            end
        | (_     , _      , []         ) -> invalid_arg "Regexp: group error."
      in
      let re = build_re [] (Acc []) ts in
      (re, Array.of_list (List.rev !refs))

    (** Exception raised when a regexp cannot be parsed. *)
    exception Regexp_error of buffer * int

    (** [regexp_error buf pos] raises the exception [Regexp_error(buf,pos)].
        It is only used internally, it is not given in the interface. *)
    let regexp_error : type a. buffer -> int -> a = fun buf pos ->
      raise (Regexp_error(buf, pos))

    (** [string_of_char_list cs] converts a list of characters into a
        [string] using a [Buffer.t]. *)
    let string_of_char_list : char list -> string = fun cs ->
      let b = Buffer.create 10 in
      List.iter (Buffer.add_char b) cs;
      Buffer.contents b

    (* [read_regexp re buf pos] input characters according to the regexp [re]
       in the buffer [buf] at the position [pos]. The value returned is the
       buffer and position after the input has been read successfully. In
       case of problem, the exception [Regexp_error] is raised. *)
    let read_regexp : regexp -> buffer -> int -> buffer * int =
      fun re buf pos ->
        let rec sread_regexp re buf pos cs =
          (*
          Printf.eprintf "%d:%d -> %a -> %C\n%!"
            (line_num buf) pos print_regexp re (get buf pos);
          *)
          match re with
          | Chr(ch)    ->
              let (c, buf, pos) = read buf pos in
              if c = ch then (c::cs, buf, pos)
              else regexp_error buf pos
          | Set(chs)   ->
              let (c, buf, pos) = read buf pos in
              if Charset.mem chs c then (c::cs, buf, pos)
              else regexp_error buf pos
          | Seq(r::rs) ->
              let (cs, buf, pos) = sread_regexp r buf pos cs in
              sread_regexp (Seq(rs)) buf pos cs
          | Seq([])    -> (cs, buf, pos)
          | Alt(r::rs) ->
              begin
                try sread_regexp r buf pos cs
                with Regexp_error(_,_) -> sread_regexp (Alt(rs)) buf pos cs
              end
          | Alt([])    -> regexp_error buf pos
          | Opt(r)     ->
              begin
                try sread_regexp r buf pos cs
                with Regexp_error(_,_) -> (cs, buf, pos)
              end
          | Str(r)     ->
              begin
                try
                  let (cs, buf, pos) = sread_regexp r buf pos cs in
                  sread_regexp re buf pos cs
                with Regexp_error(_,_) -> (cs, buf, pos)
              end
          | Pls(r)     ->
              let (cs, buf, pos) = sread_regexp r buf pos cs in
              sread_regexp (Str(r)) buf pos cs
          | Sav(r,ptr) ->
              let cs0 = cs in
              let rec fn acc = function
                | cs when cs == cs0 -> string_of_char_list acc
                | c::cs -> fn (c::acc) cs
                | [] -> assert false
              in
              let (cs, _, _ as res) = sread_regexp r buf pos cs in
              ptr := fn [] cs; res
        in
        let rec read_regexp re buf pos =
          (*
          Printf.eprintf "%d:%d -> %a -> %C\n%!"
            (line_num buf) pos print_regexp re (get buf pos);
          *)
          match re with
          | Chr(ch)    ->
              let (c, buf, pos) = read buf pos in
              if c = ch then (buf, pos)
              else regexp_error buf pos
          | Set(chs)   ->
              let (c, buf, pos) = read buf pos in
              if Charset.mem chs c then (buf, pos)
              else regexp_error buf pos
          | Seq(r::rs) ->
              let (buf, pos) = read_regexp r buf pos in
              read_regexp (Seq(rs)) buf pos
          | Seq([])    -> (buf, pos)
          | Alt(r::rs) ->
              begin
                try read_regexp r buf pos
                with Regexp_error(_,_) -> read_regexp (Alt(rs)) buf pos
              end
          | Alt([])    -> regexp_error buf pos
          | Opt(r)     ->
              begin
                try read_regexp r buf pos
                with Regexp_error(_,_) -> (buf, pos)
              end
          | Str(r)     ->
              begin
                try
                  let (buf, pos) = read_regexp r buf pos in
                  read_regexp re buf pos
                with Regexp_error(_,_) -> (buf, pos)
              end
          | Pls(r)     ->
              let (buf, pos) = read_regexp r buf pos in
              read_regexp (Str(r)) buf pos
          | Sav(r,ptr) ->
             let (cs, buf, pos) = sread_regexp r buf pos [] in
             ptr := string_of_char_list (List.rev cs);
             (buf, pos)
        in
        read_regexp re buf pos
  end


exception Preprocessor_error of string * string
let pp_error : type a. string -> string -> a =
  fun name msg -> raise (Preprocessor_error (name, msg))

module type Preprocessor =
  sig
    (** Type for the internal state of the preprocessor. *)
    type state

    (** Initial state of the preprocessor. *)
    val initial_state : state

    (** [update st name lnum line] takes as input the state [st] of the
        preprocessor, the file name [name], the number of the next input
        line [lnum] and the next input line [line] itself. It returns a
        tuple of the new state, the new file name, the new line number,
        and a boolean. The new file name and line number can be used to
        implement line number directives. The boolean is [true] if the
        line should be part of the input (i.e. it is not a specific
        preprocessor line) and [false] if it should be ignored. The
        function may raise [Preprocessor_error msg] in case of error. *)
    val update : state -> string -> int -> string
                 -> state * string * int * bool

    (** [check_final st name] check that [st] indeed is a correct state
        of the preprocessor for the end of input of file [name]. If it
        is not the case, then the exception [Preprocessor_error msg] is
        raised. *)
    val check_final : state -> string -> unit
  end

module Make(PP : Preprocessor) =
  struct
    let from_fun : ('a -> unit) -> string -> ('a -> string) -> 'a -> buffer =
      fun finalise name get_line file ->
        let rec fn name lnum loff st cont =
          let lnum = lnum + 1 in
          try
            let data = get_line file in
            let (st, name, lnum, take) = PP.update st name lnum data in
            if take then
              let llen = String.length data in
              { is_eof = false ; lnum ; loff ; llen ; data ; name
              ; next = lazy (fn name lnum (loff + llen) st cont)
              ; uid = new_uid () }
            else
              fn name lnum loff st cont
          with End_of_file -> finalise file; cont name lnum loff st
        in
        lazy
          begin
            let cont name lnum loff st =
              PP.check_final st name;
              Lazy.force (empty_buffer name lnum loff)
            in
            fn name 0 0 PP.initial_state cont
          end
  end

module NoPP : Preprocessor =
  struct
    type state = unit
    let initial_state = ()
    let update st fname lnum _ = (st, fname, lnum, true)
    let check_final _ _ = ()
  end


let define_directive =
  Str.regexp "[ \t]*define[ \t]*\\([^ \t]*\\)[ \t]*\\([^ \n\t\r]*\\)[ \t]*"

let if_directive =
  Str.regexp "[ \t]*if"

let ifdef_directive =
  Str.regexp "[ \t]*if[ \t]*def[ \t]*\\([^ \t]*\\)[ \t]*"

let ifundef_directive =
  Str.regexp "[ \t]*if[ \t]*ndef[ \t]*\\([^ \t]*\\)[ \t]*"

let ifversion_directive =
  Str.regexp "[ \t]*if[ \t]*version[ \t]*\\([<>=]*\\)[ \t]*\\([0-9]+\\)[.]\\([0-9]+\\)[ \t]*"

let else_directive =
  Str.regexp "[ \t]*else[ \t]*"

let elif_directive =
  Str.regexp "[ \t]*elif[ \t]*"

let endif_directive =
  Str.regexp "[ \t]*endif[ \t]*"

let line_num_directive =
  Str.regexp "[ \t]*\\([0-9]+\\)[ \t]*\\([\"]\\([^\"]*\\)[\"]\\)?[ \t]*$"

let test_directive fname num line =
  if Str.string_match ifdef_directive line 1 then
    let macro_name = Str.matched_group 1 line in
    try ignore (Sys.getenv macro_name); true with Not_found -> false
  else if Str.string_match ifundef_directive line 1 then
    let macro_name = Str.matched_group 1 line in
    try ignore (Sys.getenv macro_name); false with Not_found -> true
  else if Str.string_match ifversion_directive line 1 then
    let predicat = Str.matched_group 1 line in
    let major' = Str.matched_group 2 line in
    let minor' = Str.matched_group 3 line in
    try
      let predicat =
        match predicat with
        | "<>" -> (<>) | "=" -> (=) | "<" -> (<)
        | ">" -> (>) | "<=" -> (<=) | ">=" -> (>=)
        | _ -> raise Exit
      in
      let version =
        try
          Sys.getenv "OCAMLVERSION"
        with
          Not_found -> Sys.ocaml_version
      in
      let major, minor =
        match  Str.split (Str.regexp_string ".") version with
        | major ::  minor :: _ ->
           let major = int_of_string major in
           let minor = int_of_string minor in
           major, minor
        | _ -> assert false
      in
      predicat (major, minor) (int_of_string major', int_of_string minor')
    with _ ->
      Printf.eprintf "file: %s, line %d: bad predicate version\n%!" fname num;
      exit 1
  else (
    Printf.eprintf "file: %s, line %d: unknown #if directive\n%!" fname num;
    exit 1)

module OCamlPP : Preprocessor =
  struct
    type state = bool list

    let initial_state = []

    let active : state -> bool = fun st -> not (List.mem false st)

    let update st name lnum line =
      if line <> "" && line.[0] = '#' then
        if Str.string_match define_directive line 1 && active st then
          let macro_name = Str.matched_group 1 line in
          let value = Str.matched_group 2 line in
          Unix.putenv macro_name value;
          (st, name, lnum, false)
        else if Str.string_match if_directive line 1 then
          (test_directive name lnum line :: st, name, lnum, false)
        else if Str.string_match elif_directive line 1 then
          match st with
          | []      -> pp_error name "unexpected elif directive"
          | _ :: st -> (test_directive name lnum line :: st, name, lnum, false)
        else if Str.string_match else_directive line 1 then
          match st with
          | []      -> pp_error name "unexpected else directive"
          | b :: st -> (not b :: st, name, lnum, false)
        else if Str.string_match endif_directive line 1 then
          match st with
          | []      -> pp_error name "unexpected endif directive"
          | _ :: st -> (st, name, lnum, false)
        else if Str.string_match line_num_directive line 1 then
          let lnum = int_of_string (Str.matched_group 1 line) in
          let name = try Str.matched_group 3 line with Not_found -> name in
          (st, name, lnum, false)
        else
          pp_error name "unexpected directive"
      else (st, name, lnum, active st)

    let check_final st name =
      match st with
      | [] -> ()
      | _  -> pp_error name "unclosed conditionals"
  end

module DefaultPP = Make(OCamlPP)
let buffer_from_fun ?(finalise=(fun _ -> ())) fname get_line data =
  DefaultPP.from_fun finalise fname get_line data


external unsafe_input : in_channel -> string -> int -> int -> int
                      = "caml_ml_input"

external input_scan_line : in_channel -> int = "caml_ml_input_scan_line"

let input_line chan =
  let rec build_result buf pos = function
    [] -> buf
  | hd :: tl ->
      let len = String.length hd in
      String.blit hd 0 buf (pos - len) len;
      build_result buf (pos - len) tl in
  let rec scan accu len =
    let n = input_scan_line chan in
    if n = 0 then begin                   (* n = 0: we are at EOF *)
      match accu with
        [] -> raise End_of_file
      | _  -> build_result (Bytes.create len) len accu
    end else if n > 0 then begin          (* n > 0: newline found in buffer *)
      let res = Bytes.create n in
      ignore (unsafe_input chan res 0 n);
      match accu with
        [] -> res
      |  _ -> let len = len + n in
              build_result (Bytes.create len) len (res :: accu)
    end else begin                        (* n < 0: newline not found *)
      let beg = Bytes.create (-n) in
      ignore(unsafe_input chan beg 0 (-n));
      scan (beg :: accu) (len - n)
    end
  in scan [] 0

let buffer_from_channel ?(filename="") ch =
  buffer_from_fun filename input_line ch

let buffer_from_file filename =
  let ch = open_in filename in
  buffer_from_fun ~finalise:close_in filename input_line ch

let get_string_line (str, p) =
  let len = String.length str in
  let start = !p in
  if start >= len then raise End_of_file;
  while (!p < len && str.[!p] <> '\n') do
    incr p
  done;
  if !p < len then incr p;
  let len' = !p - start in
  String.sub str start len'

let buffer_from_string ?(filename="") str =
  let data = (str, ref 0) in
  buffer_from_fun filename get_string_line data

type 'a buf_table = (line * int * 'a list) list

let empty_buf = []

let eq_buf (lazy b1) (lazy b2) = b1.uid = b2.uid

let cmp_buf (lazy b1) (lazy b2) = b1.uid - b2.uid

let buf_ident (lazy buf) = buf.uid

let leq_buf b1 i1 b2 i2 =
  match (b1, b2) with
    ({ uid=ident1; }, { uid=ident2; }) ->
      (ident1 = ident2 && i1 <= i2) || ident1 < ident2

let insert_buf buf pos x tbl =
  let buf = Lazy.force buf in
  let rec fn acc = function
  | [] -> List.rev_append acc [(buf, pos, [x])]
  | ((buf',pos', y as c) :: rest) as tbl ->
     if pos = pos' && buf.uid = buf'.uid then
       List.rev_append acc ((buf', pos', (x::y)) :: rest)
     else if leq_buf buf pos buf' pos' then
       List.rev_append acc ((buf, pos, [x]) :: tbl)
     else fn (c::acc) rest
  in
  fn [] tbl

let pop_firsts_buf = function
  | [] -> raise Not_found
  | (buf,pos,l)::rest -> Lazy.from_val buf,pos,l,rest

let iter_buf buf fn =
  List.iter (fun (_,_,l) -> List.iter fn l) buf
