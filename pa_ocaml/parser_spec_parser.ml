(* Copyright 2016-2020 Christophe Raffalli & Rodolphe Lepigre. *)

open Earley_core
open Pa_ocaml_prelude
open Pa_lexing
open Parser_spec_ast
open Ast_helper

#define LOCATE locate

let expr_arg = expression_lvl (NoMatch, next_exp App)

(** Grammar for a singler parser atom. *)
let parser parser_atom =
  (* Atoms using a special, capitalized identifier. *)
  | uid:''[A-Z]+'' ov:expr_arg? $ oe:parser_param? ->
      Ppelt_atom(Location.mkloc uid _loc_uid, ov, oe)
  (* Atoms using literals syntax. *)
  | c:char_litteral oe:parser_param? ->
      Ppelt_char(c, oe)
  | s:string_litteral oe:parser_param? ->
      Ppelt_string(fst s, oe)
  | s:regexp_litteral oe:parser_param? ->
      Ppelt_regexp(s, false, oe)
  | s:new_regexp_litteral oe:parser_param? ->
      Ppelt_regexp(s, true , oe)
  (* Atoms defined by OCaml values. *)
  | id:value_path ->
      Ppelt_expr(Exp.ident ~loc:_loc (Location.mkloc id _loc))
  | "(" e:expression ")" ->
      Ppelt_expr(e)
  (* Full grammar as an atom. *)
  | '{' g:parser_grammar '}' ->
      Ppelt_grammar(g)
  (* Special atom to forbid blanks. *)
  | dash oe:parser_param? ->
      Ppelt_noblank(oe)

(** Grammar for an expression in square brackets, used for parameters. *)
and parser parser_param =
  | '[' expression ']'

(** Grammar for a modifier (e.g., Kleene star) and an optional parameter. *)
and parser parser_modifier =
  | {'*' -> Ppmod_star | '+' -> Ppmod_plus | '?' -> Ppmod_opt} parser_param?

(** Grammar for an optional greedy modifier. *)
and parser parser_greedy =
  | '$'[true]?[false]

(** Grammar for a naming pattern (for parser elements). *)
and parser parser_pattern =
  | (pattern_lvl (true, ConstrPat)) ':'

(** Grammar for a full parsing rule element. *)
and parser parser_rule_element =
  | p:parser_pattern? a:parser_atom m:parser_modifier? g:parser_greedy ->
      mk_parser_element ~loc:_loc p a m g

(** Grammar for a full parsing rule LHS. *)
and parser parser_rule_lhs = parser_rule_element+

(** Grammar for a sequence of let-bindings (allowed before rules). *)
and parser parser_rule_let_bindings =
  | let_kw r:rec_flag b:let_binding in_kw l:parser_rule_let_bindings ->
      fun x -> Exp.let_ ~loc:_loc r b (l x)
  | EMPTY ->
      fun x -> x

(** Grammar for a parsing rule guard. *)
and parser parser_rule_guard = _:when_kw expression

(** Grammar for a parsing rule semantic action. *)
and parser parser_rule_action alm =
  | "->>" r:(parser_rule alm) ->
      Ppact_dseq(r)
  | "->" a:(if alm then expression else expression_lvl (Let, Seq)) no_semi ->
      Ppact_action(a)
  | EMPTY ->
      Ppact_default

(** Grammar for a full parsing rule. *)
and parser parser_rule alm =
  | def:parser_rule_let_bindings lhs:parser_rule_lhs guard:parser_rule_guard?
    act:(parser_rule_action alm) ->
      mk_parser_rule ~loc:_loc def lhs guard act

(** Grammar for an optional tag that disables sharing. *)
and parser parser_rule_unshared =
  | {'@' | '[' '@' "unshared" ']'} -> true
  | EMPTY                          -> false

(** Grammar for a parsing rule possibly marked as non-sharable. *)
and parser parser_full_rule alm =
  | parser_rule_unshared (parser_rule alm)

(** Grammar for an alternative between several rules (main entry point). *)
and parser parser_grammar =
  | '|'? rs:{(parser_full_rule false) '|'}* r:(parser_full_rule true) ->
      mk_grammar ~loc:_loc (r::rs) (* FIXME preserve order. *)

(** Grammar for a parser binding specification. *)
let parser parser_spec =
  | name:lident args:pattern* prio:{'@' pattern}? ty:{':' typexpr}? '='
    gram:parser_grammar ->
      mk_parser_spec (Location.mkloc name _loc_name) args prio ty gram

(** Grammar for a sequence of definition bindings, starting with a parser. *)
let parser parser_bindings =
  | obs:{_:and_kw let_binding}?[[]] ->
      List.map mk_parser_binding_ocaml obs
  | and_kw obs:{let_binding _:and_kw}?[[]] parser_kw ps:parser_spec
    bs:parser_bindings ->
      List.map mk_parser_binding_ocaml obs @
      mk_parser_binding_parser ~loc:_loc_ps ps :: bs

(** New entry point in structures: parser definition. *)
let parser parser_structure =
  | _:let_kw _:parser_kw b:parser_spec bs:parser_bindings ->
      let b = mk_parser_binding_parser ~loc:_loc_b b in
      mk_parser_bindings ~loc:_loc (b :: bs)

(** New entry point in expressions: parser expression. *)
let parser parser_expression =
  | args:{_:fun_kw (pattern_lvl(false,AtomPat))* '@' pattern "->"}?
    _:parser_kw gram:parser_grammar ->
      let (args, prio) =
        match args with
        | None            -> ([]  , None      )
        | Some(args,prio) -> (args, Some(prio))
      in
      mk_parser_expr ~loc:_loc args prio gram
