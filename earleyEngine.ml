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

open EarleyUtils
open Input

let _ = Printexc.record_backtrace true

(* Flags. *)
let debug_lvl  = ref 0
let warn_merge = ref true

exception Error

type blank = buffer -> int -> buffer * int

type info = bool * Charset.t

type position = buffer * int

type errpos = {
  mutable position : position;
  mutable messages : (unit -> string) list
}

let init_errpos buf pos = { position = (buf, pos); messages = [] }

(* type for action with or without position and its combinators *)
type _ pos =
  | Idt : ('a -> 'a) pos
  | Simple : 'a -> 'a pos
  | WithPos : (buffer -> int -> buffer -> int -> 'a) -> 'a pos

(* only one identity to benefit from physical equality *)
let idt x = x

type pos2 = { buf : buffer; pos : int; buf_ab  : buffer; pos_ab : int }

let eq_pos {buf;pos} {buf=buf';pos=pos'} =
  buffer_equal buf buf' && pos = pos'

let eq_pos1 {buf;pos} (buf',pos') =
  buffer_equal buf buf' && pos = pos'

let apply_pos: type a.a pos -> position -> position -> a =
  fun f p p' ->
    match f with
    | Idt -> idt
    | Simple f -> f
    | WithPos f -> f (fst p) (snd p) (fst p') (snd p')

let fix_begin : type a.a pos -> position -> a pos =
  fun f p ->
    match f with
    | WithPos f -> let f = f (fst p) (snd p) in
                   WithPos (fun _ _ p1 p2 -> f p1 p2)
    | x -> x

let apply_pos_debut =
  fun f ({ buf; pos; buf_ab; pos_ab } as d) pos1 pos_ab1 ->
  if eq_pos1 d pos1 then apply_pos f pos_ab1 pos_ab1
  else apply_pos f (buf_ab, pos_ab) pos1

let app_pos:type a b.(a -> b) pos -> a pos -> b pos = fun f g ->
  match f,g with
  | Idt, _ -> g
  | Simple f, Idt -> Simple(f idt)
  | WithPos f, Idt -> WithPos(fun b p b' p' -> f b p b' p' idt)
  | Simple f, Simple g -> Simple(f g)
  | Simple f, WithPos g -> WithPos(fun b p b' p' -> f (g b p b' p'))
  | WithPos f, Simple g -> WithPos(fun b p b' p' -> f b p b' p' g)
  | WithPos f, WithPos g -> WithPos(fun b p b' p' -> f b p b' p' (g b p b' p'))

let compose:type a b c.(b -> c) pos -> (a -> b) pos -> (a -> c) pos = fun f g ->
  match f,g with
  | Idt, _ -> g
  | _, Idt -> f
  | Simple f, Simple g -> Simple(fun x -> f (g x))
  | Simple f, WithPos g -> WithPos(fun b p b' p' x -> f (g b p b' p' x))
  | WithPos f, Simple g -> WithPos(fun b p b' p' x -> f b p b' p' (g x))
  | WithPos f, WithPos g -> WithPos(fun b p b' p' x -> f b p b' p' (g b p b' p' x))

let compose3 f g h = compose f (compose g h)

let pos_apply : type a b.(a -> b) -> a pos -> b pos =
  fun f a ->
    match a with
    | Idt -> Simple(f idt)
    | Simple g -> Simple(f g)
    | WithPos g -> WithPos(fun b p b' p' -> f (g b p b' p'))

let pos_apply2 : type a b c.(a -> b -> c) -> a pos -> b pos -> c pos =
   fun f a b ->
     let a : a pos = match a with Idt -> Simple idt | a -> a
     and b : b pos = match b with Idt -> Simple idt | b -> b in
    match a, b with
    | Idt, _ -> assert false
    | _, Idt -> assert false
    | Simple g, Simple h -> Simple(f g h)
    | WithPos g, Simple h  -> WithPos(fun b p b' p' -> f (g b p b' p') h)
    | Simple g, WithPos h  -> WithPos(fun b p b' p' -> f g (h b p b' p'))
    | WithPos g, WithPos h  -> WithPos(fun b p b' p' -> f (g b p b' p') (h b p b' p'))

let pos_apply3 : type a b c d.(a -> b -> c -> d) -> a pos -> b pos -> c pos -> d pos =
  fun f a b c -> app_pos (pos_apply2 f a b) c

let cns : type a b c.a -> (b -> c) -> ((a -> b) -> c) = fun a f g -> f (g a)

let eq_res = eq_closure

(** A BNF grammar is a list of rules. The type parameter ['a] corresponds to
    the type of the semantics of the grammar. For example, parsing using a
    grammar of type [int grammar] will produce a value of type [int]. *)
type 'a input = buffer -> int -> 'a * buffer * int
type 'a input2 = buffer -> int -> 'a input
type 'a test  = buffer -> int -> buffer -> int -> 'a * bool

module rec Types : sig
  type 'a grammar = info Fixpoint.t * 'a rule list

   and _ symbol =
     | Term : Charset.t * 'a input -> 'a symbol
     (** terminal symbol just read the input buffer *)
     | Greedy : info Fixpoint.t * (errpos -> blank -> 'a input2) -> 'a symbol
     (** terminal symbol just read the input buffer *)
     | Test : Charset.t * 'a test -> 'a symbol
     (** test *)
     | NonTerm : info Fixpoint.t * 'a rule list ref -> 'a symbol
   (** non terminal trough a reference to define recursive rule lists *)

   (** BNF rule. *)
   and _ prerule =
     | Empty : 'a pos -> 'a prerule
     (** Empty rule. *)
     | Dep : ('a -> 'b rule) -> ('a -> 'b) prerule
     (** Dependant rule *)
     | Next : info Fixpoint.t * string * 'a symbol * ('a -> 'b) pos * ('b -> 'c) rule -> 'c prerule
   (** Sequence of a symbol and a rule. then bool is to ignore blank after symbol. *)

   (* Each rule old assoc cell to associate data to the rule in O(1).
   the type of the associat    ed data is not known ... *)
   and 'a rule = { rule : 'a prerule ; cell : 'a StackContainer.container; adr : int }

   (* type paragé par les deux types ci-dessous *)
   and ('a,'b,'c,'r) cell = {
      debut : pos2;                         (* position in the buffer, before and after blank
                                               None if nothing was parsed *)
      stack : ('c, 'r) stack;               (* tree of stack of what should be do after reading
                                               the rule *)
      acts  : 'a;                           (* action to produce the final 'c. either
                                               ('b -> 'c) or ('x -> 'b -> 'c) pos *)
      rest  : 'b rule;                      (* remaining to parse, will produce 'b *)
      full  : 'c rule;                      (* full rule. rest is a suffix of full.
                                               only use as a reference *)
     }

   (* next element of an earley stack *)
   and (_,_) element =
     (* cons cell of the stack *)
     | C : (('a -> 'b -> 'c) pos, 'b, 'c, 'r) cell -> ('a,'r) element
     (* end of the stack *)
     | B : ('a -> 'b) pos -> ('a,'b) element

   and ('a,'b) stack = ('a,'b) element list ref

   (* head of the stack *)
   and _ final = D : (('b -> 'c), 'b, 'c, 'r) cell -> 'r final

(** stack in construction ... they have a hook ! *)
   type ('a,'b) pre_stack =
     { stack : ('a, 'b) stack
     ; mutable hooks : (('a, 'b) element -> unit) list }

end = Types

and StackContainer : Container.Param
                   with type ('b,'a) elt = ('a,'b) Types.pre_stack =
  Container.Make(struct type ('b,'a) elt = ('a,'b) Types.pre_stack end)

include Types

(* INVARIANTS:

1° Consider two C elements (or two D elements) of a stack.  If their
   have the same debut, rest and full is means we have parsed the same
   prefix of the rule from debut to produce a value of the same type.

   Then, the two cell MUST HAVE PHYSICALLY EQUAL stack

2° For D nodes only, we keep only one for each (debut, rest, full) triple
   so acts are necessarily physically equal
*)

let count_rule = ref 0
let mkrule : type a. a prerule -> a rule = fun rule ->
  let adr = let c = !count_rule in count_rule := c+1; c in
  { rule; cell = StackContainer.create (); adr  }

let eq_rule : type a b. a rule -> b rule -> (a, b) eq =
  fun r1 r2 -> if Obj.repr r1 == Obj.repr r2 then  Obj.magic Eq else Neq (* r1.eq r2*)

let eq_C c1 c2 = c1 == c2
(* never worst !
  let res =
    match c1, c2 with
    (C {debut; rest; full; stack; acts},
     C {debut=d'; rest=r'; full=fu'; stack = stack'; acts = acts'}) ->
    begin
      match eq_pos debut d', eq_rule rest r', eq_rule full fu' with
      | true, Eq, Eq -> assert (stack == stack'); eq_closure acts acts'
      | _ -> false
    end
  | (B acts, B acts') -> eq_closure acts acts'
  | _ -> false
  in
  if res then assert (c1 == c2);
  res
 *)

let eq_D (D {debut; rest; full; stack; acts})
         (D {debut=debut'; rest=rest'; full=full'; stack=stack'; acts=acts'}) =
  eq_pos debut debut' &&
    match eq_rule rest rest', eq_rule full full' with
    | Eq, Eq -> assert(acts == acts'); assert(stack == stack'); true
    | _ -> false

let idtEmpty : type a.unit -> (a->a) rule = fun () -> mkrule (Empty Idt)

let new_name =
  let c = ref 0 in
  (fun () ->
    let x = !c in
    c := x + 1;
    "G__" ^ string_of_int x)

let grammar_to_rule : type a.?name:string -> a grammar -> a rule = fun ?name (i,g) ->
  match g with
  | [r] when name = None -> r
  | _ ->
     let name = match name with None -> new_name () | Some n -> n in
     mkrule (Next(i,name,NonTerm(i,ref g),Idt,idtEmpty ()))

let iter_rules : type a.(a rule -> unit) -> a rule list -> unit = List.iter

let force = Fixpoint.force

let empty = Fixpoint.from_val (true, Charset.empty)
let any = Fixpoint.from_val (true, Charset.full)

(* managment of info = accept empty + charset accepted as first char *)
let rec rule_info:type a.a rule -> info Fixpoint.t = fun r ->
  match r.rule with
  | Next(i,_,_,_,_) -> i
  | Empty _ -> empty
  | Dep(_) -> any

let symbol_info:type a.a symbol -> info Fixpoint.t  = function
  | Term(i,_) -> Fixpoint.from_val (false,i)
  | NonTerm(i,_) | Greedy(i,_) -> i
  | Test(set,_) -> Fixpoint.from_val (true, set)

let compose_info i1 i2 =
  let i1 = symbol_info i1 in
  match i2.rule with
    Empty _ -> i1
  | _ ->
     let i2 = rule_info i2 in
     Fixpoint.from_fun2 i1 i2 (fun (accept_empty1, c1 as i1) (accept_empty2, c2) ->
       if not accept_empty1 then i1 else
         (accept_empty1 && accept_empty2, Charset.union c1 c2))

let grammar_info:type a.a rule list -> info Fixpoint.t = fun g ->
  let or_info (accept_empty1, c1) (accept_empty2, c2) =
    (accept_empty1 || accept_empty2, Charset.union c1 c2)
  in
  let g = List.map rule_info g in
  Fixpoint.from_funl g (false, Charset.empty) or_info

(* affichage *)
let rec print_rule : type a.out_channel -> a rule -> unit = fun ch rule ->
    match rule.rule with
    | Next(_,name,_,_,rs) -> Printf.fprintf ch "%s %a" name print_rule rs
    | Dep _ -> Printf.fprintf ch "DEP"
    | Empty _ -> ()

let print_pos1 ch (buf, pos) =
  Printf.fprintf ch "%d:%d" (line_num buf) pos

let print_pos2 ch {buf; pos} =
  Printf.fprintf ch "%d:%d" (line_num buf) pos

let print_final ch (D {rest; full}) =
  let rec fn : type a.a rule -> unit = fun rule ->
    (match eq_rule rule rest with Eq -> Printf.fprintf ch "* " | Neq -> ());
    match rule.rule with
    | Next(_,name,_,_,rs) -> Printf.fprintf ch "%s " name; fn rs
    | Dep _ -> Printf.fprintf ch "DEP"
    | Empty _ -> ()
  in
  fn full;
  let (ae,set) = force (rule_info rest) in
  if !debug_lvl > 0 then Printf.fprintf ch "(%a %b)" Charset.print set ae

let print_element : type a b.out_channel -> (a,b) element -> unit = fun ch el ->
  let rec fn : type a b.a rule -> b rule -> unit = fun rest rule ->
    (match eq_rule rule rest with Eq -> Printf.fprintf ch "* " | Neq -> ());
    match rule.rule with
    | Next(_,name,_,_,rs) -> Printf.fprintf ch "%s " name; fn rest rs
    (*    | Dep _ -> Printf.fprintf ch "DEP "*)
    | Dep _ -> Printf.fprintf ch "DEP"
    | Empty _ -> ()
  in
  match el with
  | C {rest; full} ->
     fn rest full;
     let (ae,set) = force (rule_info rest) in
     if !debug_lvl > 0 then Printf.fprintf ch "(%a %b)" Charset.print set ae
  | B _ ->
    Printf.fprintf ch "B"

(* heart of earley: stack managment *)
type 'a sct = 'a StackContainer.table

let hook_assq : type a b. a rule -> b sct -> ((a, b) element -> unit) -> unit =
  fun r dlr f ->
    try
      let {stack; hooks } as p = StackContainer.find dlr r.cell in
      p.hooks <- f::hooks; List.iter f !stack
    with Not_found ->
      StackContainer.add dlr r.cell {stack = ref []; hooks = [f]}

(* ajout d'un element dans une pile *)
let add_assq : type a b. a rule -> (a, b) element  -> b sct -> (a, b) stack =
  fun r el dlr ->
    try
      let { stack; hooks } = StackContainer.find dlr r.cell in
      if not (List.exists (eq_C el) !stack) then (
        if !debug_lvl > 3 then
          Printf.eprintf "add stack %a ==> %a\n%!"
                         print_rule r print_element el;
        stack := el :: !stack;
        List.iter (fun f -> f el) hooks); stack
    with Not_found ->
      if !debug_lvl > 3 then
        Printf.eprintf "new stack %a ==> %a\n%!" print_rule r print_element el;
      let stack = ref [el] in
      StackContainer.add dlr r.cell {stack; hooks=[]};
      stack

let find_assq : type a b. a rule -> b sct -> (a, b) stack =
  fun r dlr ->
    try
      let { stack } = StackContainer.find dlr r.cell in stack
    with Not_found ->
      let stack = ref [] in
      StackContainer.add dlr r.cell {stack; hooks=[]};
      stack

type 'a pos_tbl = (int * int * int * int, 'a final) Hashtbl.t

let elt_key : type a. a final -> int * int * int * int =
  function D { debut = {buf;pos}; rest; full } ->
    (buffer_uid buf, pos, full.adr, rest.adr)

let print_key ch (a,b,c,d) = Printf.fprintf ch "(%d,%d,%d,%d)" a b c d

let char_pos {buf;pos} = line_offset buf + pos
let elt_pos el = char_pos el.debut

let good c i =
  let (ae,set) = force i in
  if !debug_lvl > 4 then Printf.eprintf "good %C %b %a" c ae Charset.print set;
  let res = ae || Charset.mem set c in
  if !debug_lvl > 4 then Printf.eprintf " => %b\n%!" res;
  res

(* ajoute un élément dans la table et retourne true si il est nouveau *)
let add : string -> position -> char -> 'a final -> 'a pos_tbl -> bool =
  fun info pos_final c element elements ->
    let test = match element with D { rest } -> good c (rule_info rest) in
    let key = elt_key element in
    if !debug_lvl > 2 then Printf.eprintf "add from key %a (%b)\n%!"
      print_key key test;
    test && (try
      let e = Hashtbl.find elements key in
      (match e, element with
        D {debut=d; rest; full; stack; acts},
        D {debut=d'; rest=r'; full=fu'; stack = stack'; acts = acts'}
        ->
(*         if !debug_lvl > 2 then Printf.eprintf "comparing %s %a %a %d %d %b %b %b %a %a\n%!"
            info print_final e print_final element (elt_pos pos_final e) (elt_pos pos_final element) (eq_pos d d')
           (eq rest r') (eq full fu') print_res acts print_res acts';*)
        match
           eq_pos d d', eq_rule rest r', eq_rule full fu' with
         | true, Eq, Eq ->
            if not (eq_res acts acts') && !warn_merge then
              Printf.eprintf "\027[31mmerging %a %a %a\027[0m\n%!"
                      print_final element print_pos2 d print_pos1 pos_final;
            assert(stack == stack' ||
                     (Printf.eprintf "\027[31mshould be the same stack %s %a %a %a\027[0m\n%!"
                                     info print_final element print_pos2 d print_pos1 pos_final;
                                      false));
            false
         | _ -> assert false)
    with Not_found ->
         if !debug_lvl > 1 then
           begin
             let D {debut=d} = element in
             Printf.eprintf "add %s %a %a %a\n%!" info print_final element
                            print_pos2 d print_pos1 pos_final
           end;
         Hashtbl.add elements key element;
         true)

let taille : 'a final -> (Obj.t, Obj.t) element list ref -> int = fun el adone ->
  let cast_elements : type a b.(a,b) element list -> (Obj.t, Obj.t) element list = Obj.magic in
  let res = ref 1 in
  let rec fn : (Obj.t, Obj.t) element list -> unit = fun els ->
    List.iter (fun el ->
      if List.exists ((==) el) !adone then () else begin
        res := !res + 1;
        adone := el :: !adone;
        match el with
        | C {stack} -> fn (cast_elements !stack)
        | B _   -> ()
      end) els
  in
  match el with D {stack} -> fn (cast_elements !stack); !res

let update_errpos errpos (buf, pos as p) =
  let buf', pos' = errpos.position in
  if
    (match buffer_compare buf' buf with
    | 0 -> pos' < pos
    | c -> c < 0)
  then (
    if !debug_lvl > 0 then Printf.eprintf "update error: %d %d\n%!" (line_num buf) pos;
    errpos.position <- p;
    errpos.messages <- [])

let add_errmsg errpos buf pos (msg:unit->string) =
  let buf', pos' = errpos.position in
  if buffer_equal buf buf' && pos' = pos then
    if not (List.memq msg errpos.messages) then
      errpos.messages <- msg :: errpos.messages

let protect f a = try f a with Error -> ()

let combine2 : type a0 a1 a2 b bb c.(a2 -> b) -> (b -> c) pos -> (a1 -> a2) pos -> (a0 -> a1) pos -> (a0 -> c) pos =
  fun acts acts' g f ->
    pos_apply3 (fun acts' g f x -> acts' (acts (g (f x)))) acts' g f

let combine1 : type a b c d.(c -> d) -> (a -> b) pos -> (a -> (b -> c) -> d) pos =
  fun acts g -> pos_apply (fun g a -> let b = g a in fun f -> acts (f b)) g

(* phase de lecture d'un caractère, qui ne dépend pas de la bnf *)
let lecture : type a.errpos -> blank -> int -> position -> position -> a pos_tbl -> a final buf_table ref -> unit =
  fun errpos blank id pos pos_ab elements tbl ->
    if !debug_lvl > 2 then Printf.eprintf "read at %a %a (%d)\n%!" print_pos1 pos print_pos1 pos_ab id;
    Hashtbl.iter (fun _ l -> match l with
    | D {debut; stack;acts; rest; full} as element ->
       match rest.rule with
       | Next(_,_,Term (_,f),g,rest) ->
          (try
             (*Printf.eprintf "lecture at %d %d\n%!" (line_num buf0) pos0;*)
             let buf_ab, pos_ab = pos_ab in
             let a, buf, pos = f buf_ab pos_ab in
             if !debug_lvl > 1 then
               Printf.eprintf "action for terminal of %a =>" print_final element;
             let a = try apply_pos g (buf_ab, pos_ab) (buf, pos) a
               with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
             if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
             let state =
               (D {debut; stack; acts = cns a acts; rest; full})
             in
             if not (buffer_before buf pos buf_ab pos_ab)
                || not (Hashtbl.mem elements (elt_key state)) then
               tbl := insert_buf buf pos state !tbl
           with Error -> ())

       | Next(_,_,Greedy(_,f),g,rest) ->
          (try
             let buf_ab, pos_ab = pos_ab in
             if !debug_lvl > 0 then Printf.eprintf "greedy at %d %d\n%!" (line_num buf_ab) pos_ab;
             let a, buf, pos = f errpos blank (fst pos) (snd pos) buf_ab pos_ab in
             if !debug_lvl > 1 then
               Printf.eprintf "action for greedy of %a =>" print_final element;
             let a = try apply_pos g (buf_ab, pos_ab) (buf, pos) a
               with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
             if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
             let state =
               (D {debut; stack; acts = cns a acts; rest; full})
             in
             if not (buffer_before buf pos buf_ab pos_ab)
                || not (Hashtbl.mem elements (elt_key state)) then
               tbl := insert_buf buf pos state !tbl
           with Error -> ())

       | _ -> ()) elements

let taille_tables els forward =
  if !debug_lvl > 0 then
    let adone = ref [] in
    let res = ref 0 in
    Hashtbl.iter (fun _ el -> res := !res + 1 + taille el adone) els;
    iter_buf forward (fun el -> res := !res + 1 + taille el adone);
    !res
  else 0

(* fait toutes les prédictions et productions pour un element donné et
   comme une prédiction ou une production peut en entraîner d'autres,
   c'est une fonction récursive *)
let rec one_prediction_production
 : type a. a final -> a pos_tbl -> a sct -> position -> position -> char ->  unit
 = fun element0 elements dlr pos pos_ab c ->
   match element0 with
  (* prediction (pos, i, ... o NonTerm name::rest_rule) dans la table *)
   | D {debut; acts; stack; rest; full} ->

     if !debug_lvl > 1 then Printf.eprintf "predict/product for %a %C\n%!" print_final element0 c;
     match rest.rule with
     | Next(info,_,(NonTerm(_,{contents = rules})),f,rest2) when good c info ->
        let rules = List.filter (fun rule ->
                        good c (rule_info rule)) rules in
        List.iter
            (fun rule ->
              let stack = find_assq rule dlr in
              let debut = { buf=fst pos; pos=snd pos; buf_ab=fst pos_ab; pos_ab=snd pos_ab } in
              let nouveau = D {debut; acts = idt; stack; rest = rule; full = rule} in
              let b = add "P" pos c nouveau elements in
              if b then  one_prediction_production nouveau elements dlr pos pos_ab c) rules;
        let f = fix_begin f pos_ab in
        begin match rest2.rule, eq_pos1 debut pos with
        | Empty (g), false -> (* NOTE: right recursion optim is bad (and
                                 may loop) for rule with only one non
                                 terminal *)
          let g = fix_begin g (debut.buf_ab, debut.pos_ab) in
          if !debug_lvl > 1 then Printf.eprintf "RIGHT RECURSION OPTIM %a\n%!" print_final element0;
          let complete = protect (function
              | C {rest=rest2; acts=acts'; full; debut; stack} ->
                 let c = C {rest=rest2; acts=combine2 acts acts' g f; full; debut; stack} in
                 iter_rules (fun r -> ignore (add_assq r c dlr)) rules;
              | B acts' ->
                 let c = B (combine2 acts acts' g f) in
                 iter_rules (fun r -> ignore (add_assq r c dlr)) rules)
          in
          List.iter complete !stack; (* NOTE: should use hook_assq for debut = None *)
        | _ ->
           let c = C {rest=rest2; acts=combine1 acts f; full; debut; stack} in
           iter_rules (fun r -> ignore (add_assq r c dlr)) rules
        end;
     | Dep(rule) ->
       if !debug_lvl > 1 then Printf.eprintf "dependant rule\n%!";
       let a =
         let a = ref None in
         try let _ = acts (fun x -> a := Some x; raise Exit) in assert false
         with Exit ->
           match !a with None -> assert false | Some a -> a
       in
       let cc = C { debut;
                    acts = Simple (fun b f -> f (acts (fun _ -> b))); stack;
                   rest = idtEmpty (); full } in
       let rule = rule a in
       let stack' = add_assq rule cc dlr in
       let debut = { buf=fst pos; pos=snd pos; buf_ab=fst pos_ab; pos_ab=snd pos_ab } in
       let nouveau = D {debut; acts = idt; stack = stack'; rest = rule; full = rule } in
       let b = add "P" pos c nouveau elements in
       if b then one_prediction_production nouveau elements dlr pos pos_ab c

     (* production      (pos, i, ... o ) dans la table *)
     | Empty(a) ->
        (try
           if !debug_lvl > 1 then
             Printf.eprintf "action for completion of %a =>" print_final element0;
           let x = try acts (apply_pos_debut a debut pos pos_ab)
                   with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
           if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
          let complete = fun element ->
            match element with
            | C {debut; stack=els'; acts; rest; full} ->
               if !debug_lvl > 1 then
                 Printf.eprintf "action for completion test %a" print_element element;
               if good c (rule_info rest) then begin
                 if !debug_lvl > 1 then
                   Printf.eprintf "action for completion bis of %a =>" print_final element0;
                 let acts =
                   try apply_pos_debut acts debut pos pos_ab x
                   with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e
                 in
                 if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
                 let nouveau = D {debut; acts; stack=els'; rest; full } in
                 let b = add "C" pos c nouveau elements in
                 if b then one_prediction_production nouveau elements dlr pos pos_ab c
               end
            | B _ -> ()
          in
          let complete = protect complete in
          if eq_pos1 debut pos then hook_assq full dlr complete
          else List.iter complete !stack;
         with Error -> ())

       | Next(_,_,Test(s,f),g,rest) ->
          (try
             let (buf0, pos0 as j) = pos_ab in
             if !debug_lvl > 1 then Printf.eprintf "testing at %d %d\n%!" (line_num buf0) pos0;
             let (a,b) = f (fst pos) (snd pos) buf0 pos0 in
             if b then begin
                 if !debug_lvl > 1 then Printf.eprintf "test passed\n%!";
                 let x = apply_pos g j j a in
                 let nouveau = D {debut; stack; rest; full; acts = cns x acts} in
                 let b = add "T" pos c nouveau elements in
                 if b then one_prediction_production nouveau elements dlr pos pos_ab c
               end
           with Error -> ())

     | _ -> ()

exception Parse_error of Input.buffer * int * string list

let count = ref 0

let rec tail_key : type a. a rule -> int = fun rule ->
  match rule.rule with
  | Next(_,_,_,_,rest) -> tail_key rest
  | Empty _ -> rule.adr
  | Dep _ -> assert false (* FIXME *)

let parse_buffer_aux : type a.errpos -> bool -> bool -> a grammar -> blank -> buffer -> int -> a * buffer * int =
  fun errpos internal blank_after main blank buf0 pos0 ->
    let parse_id = incr count; !count in
    (* construction de la table initiale *)
    let elements : a pos_tbl = Hashtbl.create 61 in
    let r0 : a rule = grammar_to_rule main in
    let final_elt = B (Simple idt) in
    let final_key = (buffer_uid buf0, pos0, r0.adr, tail_key r0) in
    if !debug_lvl > 2 then Printf.eprintf "final_key: %a\n%!" print_key final_key;
    let s0 : (a, a) element list ref = ref [final_elt] in
    let pos = ref pos0 and buf = ref buf0 in
    let buf', pos' = blank buf0 pos0 in
    let debut = { buf = buf0; pos = pos0; buf_ab = buf'; pos_ab = pos' } in
    let pos' = ref pos' and buf' = ref buf' in
    let init = D {debut; acts = idt; stack=s0; rest=r0; full=r0 } in
    let last_success = ref [] in
    let forward = ref empty_buf in
    if !debug_lvl > 0 then Printf.eprintf "entering parsing %d at line = %d(%d), col = %d(%d)\n%!"
      parse_id (line_num !buf) (line_num !buf') !pos !pos';
    let dlr = StackContainer.create_table 101 in
    let prediction_production advance msg l =
      if advance then begin
          if !debug_lvl > 2 then Printf.eprintf "clearing tables\n%!";
          StackContainer.clear dlr;
          Hashtbl.clear elements;
          let buf'', pos'' = blank !buf !pos in
          buf' := buf''; pos' := pos'';
          update_errpos errpos (!buf', !pos');
        end;
      let c,_,_ = Input.read !buf' !pos' in
      let c',_,_ = Input.read !buf !pos in
      if !debug_lvl > 0 then Printf.eprintf "parsing %d: line = %d(%d), col = %d(%d), char = %C-%C\n%!" parse_id (line_num !buf) (line_num !buf') !pos !pos' c c';
      List.fold_left (fun cont s ->
        if add msg (!buf,!pos) c s elements then (
          one_prediction_production s elements dlr (!buf,!pos) (!buf',!pos') c;
          true)
        else cont) advance l
    in
    let search_success () =
      try
        let success = Hashtbl.find elements final_key in
        last_success := (!buf,!pos,!buf',!pos',success) :: !last_success
      with Not_found -> ()
    in

    let continue = ref (prediction_production true "I" [init]) in

    (* boucle principale *)
    while !continue do
      if !debug_lvl > 0 then Printf.eprintf "parse_id = %d, line = %d(%d), pos = %d(%d), taille =%d (%d,%d)\n%!"
        parse_id (line_num !buf) (line_num !buf') !pos !pos' (taille_tables elements !forward)
        (line_num (fst errpos.position)) (snd errpos.position);
      lecture errpos blank parse_id (!buf, !pos) (!buf', !pos') elements forward;
     let advance, l =
       try
         let (buf', pos', l, forward') = pop_firsts_buf !forward in
         let advance = not (buffer_equal !buf buf' && !pos = pos') in
         if advance then (pos := pos'; buf := buf');
         forward := forward';
         (advance, l)
       with Not_found -> (false, [])
     in
     if advance && internal then search_success ();
     continue := prediction_production advance "L" l;
    done;
    search_success ();
    (* on regarde si on a parsé complètement la catégorie initiale *)
    let parse_error () =
      if internal then
        raise Error
      else
        let buf, pos = errpos.position in
        let msgs = List.map (fun f -> f ()) errpos.messages in
        raise (Parse_error (buf, pos, msgs))
    in
    if !debug_lvl > 0 then Printf.eprintf "searching final state of %d at line = %d(%d), col = %d(%d)\n%!" parse_id (line_num !buf) (line_num !buf') !pos !pos';
    let rec fn : type a.a final -> a = function
      | D {stack=s1; rest={rule=Empty f}; acts; full=r1} ->
         (match eq_rule r0 r1 with Neq -> raise Error | Eq ->
           let x = acts (apply_pos f (buf0, pos0) (!buf, !pos)) in
           let gn : type a b. b -> (b,a) element list -> a =
            fun x l ->
              let rec hn =
                function
                | B (ls)::l ->
                   (try apply_pos ls (buf0, pos0) (!buf, !pos) x
                    with Error -> hn l)
                | C _:: l ->
                   hn l
                | [] -> raise Error
              in
              hn l
           in
           gn x !s1)
      | _ -> assert false
    in
    let a, buf, pos as result =
      let rec kn = function
        | [] -> parse_error ()
        | (b,p,b',p', elt) :: rest ->
           try
             let a = fn elt in
             if blank_after then (a, b', p') else (a, b, p)
           with
             Error -> kn rest
      in kn !last_success
    in
    StackContainer.clear dlr; (* don't forget final cleaning of assoc cell !! *)
    (* useless but clean *)
    if !debug_lvl > 0 then
      Printf.eprintf "exit parsing %d at line = %d, col = %d\n%!" parse_id (line_num buf) pos;
    result

let internal_parse_buffer : type a.errpos -> a grammar -> blank -> ?blank_after:bool -> buffer -> int -> a * buffer * int
   = fun errpos g bl ?(blank_after=false) buf pos ->
       parse_buffer_aux errpos true blank_after g bl buf pos
