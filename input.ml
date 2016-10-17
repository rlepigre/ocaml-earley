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
    type regexp =
      | Chr of char        (* Single character.                *)
      | Set of Charset.t   (* Any character in a charset.      *)
      | Seq of regexp list (* Sequence of regular expressions. *)
      | Alt of regexp list (* Alternative between regexps.     *)
      | Opt of regexp      (* Optional regexp.                 *)
      | Str of regexp      (* Zero or more times the regexp.   *)
      | Pls of regexp      (* One  or more times the regexp.   *)

    exception Regexp_error of buffer * int
    let regexp_error : type a. buffer -> int -> a = fun buf pos ->
      raise (Regexp_error(buf, pos))

    let string_of_char_list : char list -> string = fun cs ->
      let b = Buffer.create 10 in
      List.iter (Buffer.add_char b) cs;
      Buffer.contents b

    let read_regexp : regexp -> buffer -> int -> string * buffer * int =
      fun re buf pos ->
        let rec read_regexp re buf pos cs =
          match re with
          | Chr(ch)    ->
              begin
                let (c, buf, pos) = read buf pos in
                if c = ch then (c :: cs, buf, pos)
                else regexp_error buf pos
              end
          | Set(chs)   ->
              begin
                let (c, buf, pos) = read buf pos in
                if Charset.mem chs c then (c :: cs, buf, pos)
                else regexp_error buf pos
              end
          | Seq(r::rs) ->
              begin
                let (cs, buf, pos) = read_regexp re buf pos cs in
                read_regexp (Seq(rs)) buf pos cs
              end
          | Seq([])    -> (cs, buf, pos)
          | Alt(r::rs) ->
              begin
                try read_regexp r buf pos cs
                with Regexp_error(_,_) -> read_regexp (Alt(rs)) buf pos cs
              end
          | Alt([])    -> regexp_error buf pos
          | Opt(r)     ->
              begin
                try read_regexp r buf pos cs
                with Regexp_error(_,_) -> (cs, buf, pos)
              end
          | Str(r)     ->
              begin
                try
                  let (cs, buf, pos) = read_regexp r buf pos cs in
                  read_regexp (Str(r)) buf pos cs
                with Regexp_error(_,_) -> (cs, buf, pos)
              end
          | Pls(r)     ->
              begin
                let (cs, buf, pos) = read_regexp r buf pos cs in
                read_regexp (Str(r)) buf pos cs
              end
        in
        let (cs, buf, pos) = read_regexp re buf pos [] in
        (string_of_char_list (List.rev cs), buf, pos)
  end

let line_num_directive =
  Str.regexp "[ \t]*\\([0-9]+\\)[ \t]*\\([\"]\\([^\"]*\\)[\"]\\)?[ \t]*$"

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

let else_directive =
  Str.regexp "[ \t]*else[ \t]*"

let elif_directive =
  Str.regexp "[ \t]*elif[ \t]*"

let endif_directive =
  Str.regexp "[ \t]*endif[ \t]*"

type cont_info =
    Else | Endif | EndOfFile | Elif of bool

let buffer_from_fun ?(finalise=(fun _ -> ())) fname get_line data =
  let rec fn fname active num loff cont =
    begin
      let num = num + 1 in
      try
        let line = get_line data in
        let len = String.length line in
        let loff' = loff + len in
        (fun () ->
           if len > 0 && line.[0] = '#' then
             if Str.string_match line_num_directive line 1 then
               let num =
                 int_of_string (Str.matched_group 1 line)
               in
               let fname =
                 try Str.matched_group 3 line with Not_found -> fname
               in
               fn fname active num loff' cont
             else if Str.string_match define_directive line 1 then
               let macro_name = Str.matched_group 1 line in
               let value = Str.matched_group 2 line in
               Unix.putenv macro_name value;
               fn fname active num loff' cont
             else if Str.string_match if_directive line 1 then
               let b = test_directive fname num line in
               fn fname (b && active) num loff' (
                    let rec cont' b = fun fname (status:cont_info) num loff ->
                      match status with
                      | EndOfFile ->
                         Printf.eprintf "file: %s, line %d: expecting '#else' or '#endif'" fname num;
                         exit 1
                      | Endif -> fn fname active num loff cont
                      | Else ->
                         fn fname (not b && active) num loff
                            (fun fname (status:cont_info) num loff ->
                             match status with
                             | Elif _ | Else | EndOfFile ->
                                                  Printf.eprintf "file: %s, line %d: expecting '#endif'" fname num;
                                                  exit 1
                             | Endif -> fn fname active num loff cont)
                      | Elif b' ->
                         fn fname (not b && b' && active) num loff (cont' (b || b'))
                    in
                    cont' b)
             else if Str.string_match elif_directive line 1 then
               let b = test_directive fname num line in
               cont fname (Elif b) num loff'
             else if Str.string_match else_directive line 1 then
               cont fname Else num loff'
             else if Str.string_match endif_directive line 1 then
               cont fname Endif num loff'
             else if active then (
               { is_eof = false; name = fname; lnum = num; loff; llen = len ; data = line ;
                 next = lazy (fn fname active num loff' cont); uid = new_uid () })
             else fn fname active num  loff' cont
           else if active then (
               { is_eof = false; name = fname; lnum = num; loff; llen = len ; data = line ;
                 next = lazy (fn fname active num loff' cont); uid = new_uid () })
           else fn fname active num loff' cont)
      with
        End_of_file -> fun () -> finalise data; cont fname EndOfFile num loff
    end ()
  in
  lazy (fn fname true 0 0 (fun fname status line loff ->
  match status with
  | Else ->
     Printf.eprintf "file: %s, extra '#else'" fname;
     exit 1
  | Elif _ ->
     Printf.eprintf "file: %s, extra '#elif'" fname;
     exit 1
  | Endif ->
     Printf.eprintf "file: %s, extra '#endif'" fname;
     exit 1
  | EndOfFile ->
     Lazy.force (empty_buffer fname line loff)))

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
