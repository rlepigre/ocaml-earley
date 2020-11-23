(* Copyright 2016-2020 Christophe Raffalli & Rodolphe Lepigre. *)

type expr = Parsetree.expression
type patt = Parsetree.pattern
type ty = Parsetree.core_type
type vb = Parsetree.value_binding

(** Parser modifiers like the Kleene star, plus or optional marker. *)
type parser_modifier =
  | Ppmod_star
  | Ppmod_plus
  | Ppmod_opt

(** Parser elements that are sequenced to form rules. *)
type parser_element = { 
  ppelt_desc: parser_element_desc;
  (** Parser atom contained in the element. *)
  ppelt_loc: Location.t;
  (** Source code location for the element. *)
  ppelt_pat: patt option;
  (** Possible variables, bound in a semantic action. *)
  ppelt_modifier: (parser_modifier * expr option)  option;
  (** Possible parser modifier. *)
  ppelt_greedy: bool;
  (** Is the element marked as being greedy? *)
}

(** A single parser atom. *)
and parser_element_desc =
  | Ppelt_atom of string Location.loc * expr option * expr option
  (** Capitalized identifier with optional argument and optional parameter. *)
  | Ppelt_char of char * expr option
  (** Character litteral with optional semantic value. *)
  | Ppelt_string of string * expr option
  (** String litteral with optional semantic value. *)
  | Ppelt_regexp of string * bool * expr option
  (** Regexp litteral, boolean [true] if using build-in regexps. *)
  | Ppelt_expr of expr
  (** Expression as a parser. *)
  | Ppelt_grammar of parser_grammar
  (** Full grammar as a parser. *)
  | Ppelt_noblank of expr option
  (** No blank marker with optional semantic value. *)

(** Parser semantic action. *)
and parser_action =
  | Ppact_default
  (** No specific action, generate default. *)
  | Ppact_action of expr
  (** Standard semantic action build with the given expr. *)
  | Ppact_dseq of parser_rule
  (** Dependent sequence: continue parsing in the action. *)

(** A single parsing rule. *)
and parser_rule = {
  pprule_wrapper: expr -> expr;
  (** A wrapper for the generated expression (typically used for lets). *)
  pprule_pelts: parser_element list;
  (** The elements forming the rule (put in sequence). *)
  pprule_guard: expr option;
  (** Optional rule guard (controls when the rule applies). *)
  pprule_action: parser_action;
  (** The semantic action for the rule. *)
  pprule_loc: Location.t;
  (** Source code location for the rule. *)
}

(** A parser grammar. *)
and parser_grammar = {
  ppgram_rules: (bool * parser_rule) list;
  (** List of rules for the grammar, boolean [true] if unshared. *)
  ppgram_loc: Location.t;
  (** Source code location for the grammar. *)
}

(** Specification for a parser definition. *)
type parser_spec = {
  ppspec_name: string Location.loc;
  (** Name for the parser. *)
  ppspec_args: patt list;
  (** Regular arguments for the parser. *)
  ppspec_prio: patt option;
  (** Optional, special priority argument for the parser. *)
  ppspec_type: ty option;
  (** Optional type annotation for the parser. *)
  ppspec_gram: parser_grammar;
  (** Grammar for the parser. *)
}

(** Binding in a sequence of mutually defined parsers and values. *)
type parser_binding = {
  ppbind_desc: parser_binding_desc;
  (** The actual binding. *)
  ppbind_loc: Location.t;
  (** Source code location for the binding. *)
}

(** Parser or value binding. *)
and parser_binding_desc =
  | Ppbind_parser of parser_spec
  (** Parser definition binding. *)
  | Ppbind_ocaml of vb
  (** Standard value binding. *)

(** Sequence of bindings for mutually defined parsers and values. *)
type parser_bindings = {
  ppbinds_desc: parser_binding list;
  (** List of bindings. *)
  ppbinds_loc: Location.t;
  (** Source code location. *)
}

(** Parser expression (with possible parameters). *)
type parser_expr = {
  ppexpr_args: patt list;
  (** Regular arguments for the parser. *)
  ppexpr_prio: patt option;
  (** Optional, special priority argument for the parser. *)
  ppexpr_gram: parser_grammar;
  (** Grammar for the parser. *)
  ppexpr_loc: Location.t;
  (** Source code location. *)
}

let mk_parser_element ~loc pat atm md g =
  {ppelt_loc = loc; ppelt_pat = pat; ppelt_desc = atm;
  ppelt_modifier = md; ppelt_greedy = g}

let mk_parser_rule ~loc wrap elts guard act =
  {pprule_wrapper = wrap; pprule_pelts = elts; pprule_guard = guard;
  pprule_action = act; pprule_loc = loc}

let mk_grammar ~loc rules =
  {ppgram_rules = rules; ppgram_loc = loc}

let mk_parser_spec name args prio ty gram =
  {ppspec_name = name; ppspec_args = args; ppspec_prio = prio;
  ppspec_type = ty; ppspec_gram = gram}

let mk_parser_binding_ocaml b =
  {ppbind_desc = Ppbind_ocaml(b); ppbind_loc = b.pvb_loc}

let mk_parser_binding_parser ~loc ps =
  {ppbind_desc = Ppbind_parser(ps); ppbind_loc = loc}

let mk_parser_bindings ~loc pbs =
  {ppbinds_desc = pbs; ppbinds_loc = loc}

let mk_parser_expr ~loc args prio gram =
  {ppexpr_args = args; ppexpr_prio = prio; ppexpr_gram = gram;
  ppexpr_loc = loc}
