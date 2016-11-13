(** A small module for efficient regular expressions. *)

open Input

(** Type of a regular expression. *)
type regexp =
  | Chr of char        (* Single character.                *)
  | Set of Charset.t   (* Any character in a charset.      *)
  | Seq of regexp list (* Sequence of regular expressions. *)
  | Alt of regexp list (* Alternative between regexps.     *)
  | Opt of regexp      (* Optional regexp.                 *)
  | Str of regexp      (* Zero or more times the regexp.   *)
  | Pls of regexp      (* One  or more times the regexp.   *)
  | Sav of regexp * string ref     (* save what is read    *)

(** Exception that is raised when a regexp cannot be read. *)
exception Regexp_error of buffer * int

val print_regexp : out_channel -> regexp -> unit

val regexp_from_string : string -> regexp * string ref array

(** [read_regexp re buf pos] attempts to parse using the buffer [buf] at
    position [pos] using the regular expression [re]. The return value is
    a triple of the parsed string, the buffer after parsing and the
    position after parsing. The exception [Regexp_error(err_buf, err_pos]
    is raised in case of failure at the given position. *)
val read_regexp : regexp -> buffer -> int -> buffer * int
