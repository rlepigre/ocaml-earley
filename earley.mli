(*
  ======================================================================
  Copyright Christophe Raffalli & Rodolphe Lepigre
  LAMA, UMR 5127 CNRS, Université Savoie Mont Blanc

  christophe.raffalli@univ-savoie.fr
  rodolphe.lepigre@univ-savoie.fr

  This software contains a parser combinator library for the OCaml lang-
  uage. It is intended to be used in conjunction with pa_ocaml (an OCaml
  parser and syntax extention mechanism) to provide  a  fully-integrated
  way of building parsers using an extention of OCaml's syntax.

  This software is governed by the CeCILL-B license under French law and
  abiding by the rules of distribution of free software.  You  can  use, 
  modify and/or redistribute the software under the terms of the CeCILL-
  B license as circulated by CEA, CNRS and INRIA at the following URL.

      http://www.cecill.info 

  As a counterpart to the access to the source code and  rights to copy,
  modify and redistribute granted by the  license,  users  are  provided
  only with a limited warranty  and the software's author, the holder of
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

(** Earley is a parser combinator library implemented using  the  Earley
    algorithm. It focuses mainly on efficiency and  is  indended  to  be
    used in conjunction with the pa_ocaml parser  and  syntax  extention
    mechanism. *)

open Charset
open Input

(** {2 Types and exceptions} *)

(** Type of a parser (or grammar) producing a value of type ['a]. *)
type 'a grammar

(** As [Earley] does scannerless parsing, a notion of  [blank]  function
    is used to discard meaningless parts of the input (e.g. comments  or
    spaces). A [blank] function takes as input a [buffer] and a position
    (represented as an [int]) and returns a couple of a [buffer]  and  a
    position corresponding to the next meaningful character. *)
type blank = buffer -> int -> buffer * int

(** The exception [Parse_error(buf,pos,msgs)] is raised whenever parsing
    fails. It contains the position [pos] (and the corresponding  buffer
    [buf]) of the furthest reached position in the input, and a list  of
    error messages [msgs]. *)
exception Parse_error of buffer * int * string list

(** [give_up ()] can be called by the user to force the parser to reject
    a possible parsing rule. *)
val give_up : unit -> 'a

(** [handle_exception fn v] applies the function [fn] to [v] and handles
    the [Parse_error] exception. In particular, a parse error message is
    presented to the user in  case  of  a  failure,  and  the  exception
    [Failure "No parse."]. *)
val handle_exception : ('a -> 'b) -> 'a -> 'b

(** [debug_lvl] is a flag that can be set for [Earley] to display  debug
    data on [stderr]. The default value is [0], and bigger numbers acti-
    vate more and more debuging informations. *)
val debug_lvl : int ref

(** [warn_merge] is a flag that is used to choose whether  warnings  are
    or not when an ambiguity is encountered while parsing.  The  default
    value is [true]. *)
val warn_merge : bool ref

(** {2 Atomic parsers} *)

(** [char ~name c v] is a grammar that accepts only the  character  [c],
    and returns [v] as a semantic value. An optional [name] can be given
    to the grammar for reference in error messages. *)
val char : ?name:string -> char -> 'a -> 'a grammar

(** [string s v] is a grammar that accepts only the  string  [str],  and
    returns [v] as a semantic value. An optional [name] can be given  to
    the grammar for reference in error messages. *)
val string : ?name:string -> string -> 'a -> 'a grammar

(** [eof v] is a grammar that only accepts the end  of  file  character,
    and returns [v] as a semantic value. *)
val eof : 'a -> 'a grammar

(** [any] is a grammar that accepts a single character (but not the  end
    of file) and returns its value. *)
val any : char grammar

(** [in_charset cs] is a grammar that parses any character of  the  [cs]
    charset, and returns its value. An optional [name] can be  given  to
    the grammar for reference in error messages. *)
val in_charset : ?name:string -> charset -> char grammar

(** [not_in_charset cs] is similar to  [in_charset cs]  but  it  accepts
    the characters that are not in [cs]. *)
val not_in_charset : ?name:string -> charset -> unit grammar

(** [empty v] is a grammar that does not parse anything and returns  [v]
    as a semantic value. Note that this grammar never fails. *)
val empty : 'a -> 'a grammar

(** [fail ()] is a grammar that always fail, whatever the input. *)
val fail : unit -> 'a grammar

(** [error_message msg] always fails, but it adds [msg ()] to  the  list
    of error messages potentially reported by [Parse_error]. *)
val error_message : (unit -> string) -> 'a grammar

(** [black_box fn cs name] is a grammar that uses the function  [fn]  to
    parses the input buffer. [fn buf pos] should start parsing [buf]  at
    position [pos], and return a couple containing the  new  buffer  and
    position of the first unread character. The character set [cs]  must
    contain at least the characters that are accepted as first character
    by [fn], and no less. The [name] argument is used for  reference  in
    error messages. Note that the functon [fn] should  use  [give_up ()]
    in case of a parse error. *)
(*
val  black_box : (buffer -> int -> 'a * buffer * int) -> charset
                   -> string -> 'a grammar
*)
val  black_box : (buffer -> int -> 'a * buffer * int) -> charset -> bool
                   -> string -> 'a grammar

(** [debug msg] is a dummy grammar that always succeeds and prints [msg]
    on [stderr] when used. It is useful for debugging. *)
val debug : string -> unit grammar

(** {2 Blanks management} *)

(** [no_blank] is a [blank] function that does not discard any character
    of the input buffer. *)
val no_blank : blank

(** [blank_grammar gr bl] produces a [blank] function using the  grammar
    [gr] and the [blank] function [bl]. It parses as much of  the  input
    as possible using the grammar [gr] with the [blank]  function  [bl],
    and returns the reached position. *)
val blank_grammar : unit grammar -> blank -> blank

(** [change_layout ~obb ~oba gr bl] replaces the current  [blank]  func-
    tion with [bl], while parsing using the grammar [gr].  The  optional
    parameter [obb] ([true] by default) forces the  application  of  the
    new blank function, before starting to parse with  [gr].  Note  that
    the old blank function is always called before the first terminal of
    [gr]. Similarly, the optional parameter [oba]  ([true]  by  default)
    forces a call to the old blank function after the end of the parsing
    of [gr]. Note that the new blank function is always called after the
    last terminal. *)
val change_layout : ?old_blank_before:bool -> ?new_blank_after:bool
                      -> 'a grammar -> blank -> 'a grammar

(** [ignore_next_blank gr] disables the use of the blank function before
    the first terminal of [gr]. If the empty input is parsed using [gr],
    blanks are ignored in the usual  way  ([ignore_next_blank empty]  is
    equivalent to empty). *)
val ignore_next_blank : 'a grammar -> 'a grammar

(** {2 Support for recursive grammars} *)

(** [declare_grammar name] returns a new grammar that can be used in the
    definition of other grammars, but that cannot be run on input before
    it has been initialized with [set_grammar]. The [name]  argument  is
    used for reference to the grammar in error messages. *)
val declare_grammar : string -> 'a grammar

(** [set_grammar gr grdef] set the definiton of grammar [gr] (previously
    declared with [declare_grammar]) to be  [grdef].  [Invalid_argument]
    is raised if [set_grammar] is used on a grammar that was not created
    with [declare_grammar]. The behavious is undefined if a  grammar  is
    set twice with [set_grammar]. *)
val set_grammar : 'a grammar -> 'a grammar -> unit

(** {2 Parsing functions} *)

(** [parse_buffer gr bl buf] parses the buffer [buf] using  the  grammar
    [gr] and the blank function [bl]. The exception [Parse_error] may be
    raised in case of error. *)
val parse_buffer : 'a grammar -> blank -> buffer -> 'a

(** [parse_string ~filename gr bl str] parses the string [str] using the
    grammar [gr] and the blank function [bl]. An optional [filename] can
    be provided for reference  to  the  input  in  error  messages.  The
    exception [Parse_error] may be raised in case of error. *)
val parse_string : ?filename:string -> 'a grammar -> blank
                     -> string -> 'a

(** [parse_channel ~filename gr bl ch] parses the contenst of  the  input
    channel [ch] using the grammar [gr] and the blank  function  [bl].  A
    [filename] can be provided for reference to the input in case  of  an
    error. [parse_channel] may raise the [Parse_error] exception. *)
val parse_channel : ?filename:string -> 'a grammar -> blank
                      -> in_channel -> 'a

(** [parse_file gr bl fn] parses the file [fn] using the grammar [gr] and
    the blank function [bl]. The exception [Parse_error] may be raised in
    case of error. *)
val parse_file : 'a grammar -> blank -> string -> 'a

(** [partial_parse_buffer gr bl buf pos] parses  input  from  the  buffer
    [buf] starting a position [pos], using the grammar [gr] and the blank
    function [bl]. A triple is returned containing the  new  buffer,  the
    position that was reached during parsing, and the semantic result  of
    the parsing. Note that this function should not be used in the  defi-
    nition of a grammar using the [black_box] function. *)
val partial_parse_buffer : 'a grammar -> blank -> buffer -> int
                             -> 'a * buffer * int

(** A functor providing support for using and [Input] preprocessor. *)
module WithPP : functor (PP : Preprocessor) ->
  sig
    (** [parse_string] is the same as [Earley.parse_string] but  it  uses
        the preprocessor defined by [PP]. *)
    val parse_string : ?filename:string -> 'a grammar -> blank
                         -> string -> 'a

    (** [parse_channel] is the same as [Earley.parse_channel] but it uses
        the preprocessor defined by [PP]. *)
    val parse_channel : ?filename:string -> 'a grammar -> blank
                          -> in_channel -> 'a

    (** [parse_file] is the same as [Earley.parse_file] but it  uses  the
        preprocessor defined by [PP]. *)
    val parse_file : 'a grammar -> blank -> string -> 'a
  end





(** [greedy g] parses g in a greedy way: only the longest match is considered.
    Still ambigous if the longest match is not unique *)
val greedy : 'a grammar -> 'a grammar

(** {Sequencing combinators} *)

(** [sequence g1 g2 f] is a grammar that first parses using [g1], and then
    parses using [g2]. The results of the sequence is then obtained by applying
    [f] to the results of [g1] and [g2]. *)
val sequence : 'a grammar -> 'b grammar -> ('a -> 'b -> 'c) -> 'c grammar

(** [sequence_position g1 g2 f] is a grammar that first parses using [g1], and
    then parses using [g2]. The results of the sequence is then obtained by
    applying [f] to the results of [g1] and [g2], and to the positions (i.e.
    buffer and index) of the corresponding parsed input.

    Remark: [sequence g1 g2 f] is equivalent to
    [sequence_position g1 g2 (fun r1 r2 _ _ _ _ -> f r1 r2)]. *)
val sequence_position : 'a grammar -> 'b grammar
  -> ('a -> 'b -> buffer -> int -> buffer -> int -> 'c)
  -> 'c grammar

(** [fsequence g1 g2] is a grammar that first parses using [g1], and then
    parses using [g2]. The results of the sequence is then obtained by applying
    the result of [g1] to the result of [g2].

    Remark: [fsequence g1 g2] is equivalent to
    [sequence g1 g2 (fun x f -> f x)]. *)
val fsequence : 'a grammar -> ('a -> 'b) grammar -> 'b grammar

(** [fsequence_position g1 g2] is a grammar that first parses using [g1], and
    then parses using [g2]. The results of the sequence is then obtained by
    applying the result of [g1] and position information (see the definition of
    [sequence_position]) to the result of [g2]. *)
val fsequence_position : 'a grammar
  -> ('a -> buffer -> int -> buffer -> int -> 'b) grammar
  -> 'b grammar

(** [sequence3] is similar to [sequence], but it composes three grammars into
    a sequence.

    Remark: [sequence3 g1 g2 g3 f] is equivalent to
    [sequence (sequence g1 g2 f) g3 (fun f x -> f x)]. *)
val sequence3 : 'a grammar -> 'b grammar -> 'c grammar
  -> ('a -> 'b -> 'c -> 'd) -> 'd grammar


(** [conditional_sequence g1 cond g2 f] is a grammar that first parses using [g1],
    which returns a value [x], and if [cond x] does not raise Give_up, then it
    continues to parse with [g2] which returns [y] and return [f (cond x) y]. *)
val conditional_sequence : 'a grammar -> ('a -> 'b) -> 'c grammar -> ('b -> 'c -> 'd) -> 'd grammar

(** similar to the previous one, with position passed to f *)
val conditional_sequence_position : 'a grammar -> ('a -> 'b) -> 'c grammar -> ('b -> 'c -> buffer -> int -> buffer -> int -> 'd) -> 'd grammar

(** [conditional_fsequence g1 cond g2] is a grammar that first parses using [g1],
    which returns a value [x], and if [cond x] does not raise Give_up, then it
    continues to parse with [g2] and returns the result of [g2] applied to [cond x].

    Remark: [conditional_fsequence g1 cond g2] is equivalent to
    [conditional_sequence g1 cond g2 (fun x f -> f x)]. *)
val conditional_fsequence : 'a grammar -> ('a -> 'b) -> ('b -> 'c) grammar -> 'c grammar

(** similar to the previous one, with position passed to the result of g2 *)
val conditional_fsequence_position : 'a grammar -> ('a -> 'b) -> ('b -> buffer -> int -> buffer -> int -> 'c) grammar -> 'c grammar


(** [dependent_sequence g1 g2] is a grammar that first parses using [g1],
    which returns a value [x], and then continues to parse with [g2 x] and
    return its result. *)
val dependent_sequence : 'a grammar -> ('a -> 'b grammar) -> 'b grammar

val iter : 'a grammar grammar -> 'a grammar
(**  = fun g -> dependent_sequence g (fun x -> x) *)


(** [option v g] tries to parse the input as [g], and returns [v] in case of
    failure. *)
val option : 'a -> 'a grammar -> 'a grammar

val fixpoint : 'a -> ('a -> 'a) grammar -> 'a grammar
(** [fixpoint v g] parses a repetition of one or more times the input parsed
    by [g]. The value [v] is used as the initial value (i.e. to finish the
    sequence).

    if parsing X with g returns a function gX, parsing X Y Z with fixpoint a g
    will return gX (gY (gZ a)).

    This consumes stack proportinal to the input length ! use revfixpoint ...
*)

val fixpoint1 : 'a -> ('a -> 'a) grammar -> 'a grammar
(** as [fixpoint] but parses at leat once with the given grammar *)

(** [alternatives [g1;...;gn]] tries to parse using all the grammars
    [[g1;...;gn]] and keeps only the first success. *)
val alternatives : 'a grammar list -> 'a grammar

(** [apply f g] applies function [f] to the value returned by the grammar
    [g]. *)
val apply : ('a -> 'b) -> 'a grammar -> 'b grammar

(** [apply_position f g] applies function [f] to the value returned by the
    grammar [g] and the positions at the beginning and at the end of the
    input parsed input. *)
val apply_position : ('a -> buffer -> int -> buffer -> int -> 'b)
  -> 'a grammar -> 'b grammar

(** [position g] tranforms the grammar [g] to add information about the
    position of the parsed text. *)
val position : 'a grammar -> (string * int * int * int * int * 'a) grammar

(** [test c f] perform a test [f] on the input buffer. Do not parse
    anything (position are unchanged). The charset [c] should contains
    all character accepted as at the position given to f *)
val test : ?name:string -> Charset.t -> (buffer -> int -> ('a * bool)) -> 'a grammar

(** [blank_test c f] same as above except that [f] is applied to [buf'
    pos' buf pos] where [(buf', pos')] is the position before then
    blank. The charset c should contains all character accepted as at
    the position (buf,pos). This allow to test the presence of blank
    or even to read the blank and return some information *)
val blank_test : ?name:string -> Charset.t ->
  (buffer -> int -> buffer -> int -> ('a * bool)) -> 'a grammar

(** always succefull test, used internally *)
val success_test : 'a -> 'a grammar

(** a test that fails if there is no blank *)
val with_blank_test : 'a -> 'a grammar

(* an always succesful test. Useful to recover blank parsing in a rule like
   x - y? which does not parse blank after the rule is y parses nothing.
   x - y? relax works as expected *)
val relax : unit grammar




(** The too previous function allow for recursive grammar, but left recursion
    is forbidden and triggers a [Failure] exception.

    For instance the following code is incorrect:

    {[
    let p = declare_grammar ()
    let p' = sequence (sequence (option (string "a" ["a"])) p) (string "b" "b") (fun l x -> x::l)
    let _ = set_grammar p p'
    ]}
*)

(** [grammar_family to_str name] returns a pair [(gs, set_gs)], where [gs]
    is a finite family of grammars parametrized by a value of type ['a]. A name
    [name] is to be provided for the family, and an optional function [to_str]
    can be provided to print the parameter and display better error messages. *)
val grammar_family : ?param_to_string:('a -> string) -> string
  -> ('a -> 'b grammar) * (('a -> 'b grammar) -> unit)

(**
   {[
   (* Declare the grammar family *)
   let (gr, set_gr) = grammar_family to_str name in

   ... code using grammars of gr to define mutually recursive grammars ...
   ... the grammars in gr cannot be used in "left position" ...
   ... (same restriction as for declare_grammar ...

   (* Define the grammar family *)
   let _ = set_gr the_grammars

   ... now the new family can be used ...
   ]}
*)




(** [accept_empty g] returns [true] if the grammar [g] accepts the empty input
    and [false] otherwise. *)
val accept_empty : 'a grammar -> bool

val grammar_info : 'a grammar -> bool * Charset.t



(** give a name to the grammar. Usefull for debugging. *)
val give_name : string -> 'a grammar -> 'a grammar
