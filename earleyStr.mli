(** Earley support for [Str] regular expressions. *)

open Input
open Earley

(** [blank_regexp re] produces a blank function  from  the  regexp  [re] 
    (following the [Str] syntax). There is an important limitation rega-
    rding regular expressions containing the newline  character  ['\n'],
    due to the fact that the [Str] module only matches on  strings  (and
    not on an abstract notion of buffer). Such regular  expressions  can
    only be used if they are idempotent. *)
val blank_regexp : string -> buffer -> int -> buffer * int

(** [regexp ?name re g] is a grammar that parses the input according  to
    the regular expression [re], and returns a value built  by  applying
    the function [g] to a function of type [int -> string] that  returns
    the substring matched by the [n]-th match group of the  regexp  [re]
    (as in the [Str] module). The optional [name] argument  is  used  to
    refer to the regular expression in error messages. *)
val regexp : ?name:string -> string -> ((int -> string) -> 'a) -> 'a grammar
