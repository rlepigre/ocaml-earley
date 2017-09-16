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

let first_pos pos1 pos2 =
  match pos1 with
  | None -> pos2
  | Some _ -> pos1

let apply_pos_debut: type a b.a pos
                     -> (position * position) option
                     -> position -> position -> a =
  fun f debut pos pos_ab ->
    match debut with
    | None -> apply_pos f pos_ab pos_ab
    | Some(_,p) -> apply_pos f p pos

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

(* Combinators to compose actions *)
(* Cleanly tuned to correctly detect ambiguïties *)
type _ res =
  | Nil : ('a -> 'a) res
  | Cns : 'a res * ('b -> 'c) res -> (('a -> 'b) -> 'c) res
  | Sin : 'a -> 'a res
  | Cps : ('a -> 'b) res * ('b -> 'c) res -> ('a -> 'c) res
  | Csp : ('a -> 'b) res * ('c -> 'd) res -> ('a -> ('b -> 'c) -> 'd) res
  | Giv : 'a res -> (('a -> 'b) -> 'b) res

let rec print_res : type a. out_channel -> a res -> unit = fun ch r ->
  match r with
  | Nil -> Printf.fprintf ch "Nil"
  | Sin x -> Printf.fprintf ch "x"
  | Cns(x,g) -> Printf.fprintf ch "(%a::%a)" print_res x print_res g
  | Cps(f,g) -> Printf.fprintf ch "%a o %a" print_res g print_res f
  | Csp(f,g) -> Printf.fprintf ch "(y -> %a o y o %a)" print_res g print_res f
  | Giv(a)   -> Printf.fprintf ch "(f -> f %a)" print_res a

let sin : type a b. (a -> b) -> (a -> b) res = fun f ->
  match f === idt with Eq -> Nil | _ -> Sin f

let cps : type a b c.(a -> b) res * (b -> c) res -> (a -> c) res = function
  | Nil, g -> g
  | f, Nil -> f
  | (Sin f0 as f), g -> (match f0 === idt with Eq -> g | _ -> Cps(f,g))
  | f, (Sin g0 as g) -> (match g0 === idt with Eq -> f | _ -> Cps(f,g))
  | f, g -> Cps(f,g)

let cns : type a b c.a res * (b -> c) res -> ((a -> b) -> c) res = fun (a, f) ->
  match f with
  | Nil -> Giv(a)
  | Sin f0 as f -> (match f0 === idt with Eq -> Giv a | _ -> Cns(a,f))
  | f -> Cns(a,f)

let rec eq_res : type a b. a res -> b res -> bool = fun a b ->
  if eq a b then true else
    match a,b with
    | Nil, Nil -> true
    | Sin a, Sin b -> eq a b
    | Cns(a,l), Cns(b,p) -> eq a b && eq_res l p
    | Cps(f,g), Cps(h,k) -> eq_res f h && eq_res g k
    | Csp(f,g), Csp(h,k) -> eq_res f h && eq_res g k
    | Giv(a), Giv(b)     -> eq_res a b
    | _ -> false

let rec eval : type a. a res -> a =
  fun r ->
    match r with
    | Nil -> idt
    | Sin b -> b
    | _ -> assert false

let rec apply : type a b. (a -> b) res -> a res -> b res = fun r a ->
  match (r, a) with
  | Sin f   , Sin x -> Sin (f x)
  | Nil     , a     -> a
  | Cns(x,f), a     -> apply f (apply a x)
  | Cps(f,g), a     -> apply g (apply f a)
  | Csp(f,g), a     -> cns(apply f a,g)
  | Giv a   , f     -> apply f a
  | r       , a     -> assert false

(** A BNF grammar is a list of rules. The type parameter ['a] corresponds to
    the type of the semantics of the grammar. For example, parsing using a
    grammar of type [int grammar] will produce a value of type [int]. *)
type 'a input = buffer -> int -> 'a * buffer * int
type 'a input2 = buffer -> int -> 'a input
type 'a test  = buffer -> int -> buffer -> int -> 'a * bool

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
   the type of the associated data is not known ... *)
and 'a rule = ('a prerule * Container.t)


(* type paragé par les deux types ci-dessous *)
type ('a,'b,'c,'r) cell = {
  debut : (position * position) option; (* position in the buffer, before and after blank
                                           None if nothing was parsed *)
  stack : ('c, 'r) element list ref;    (* tree of stack of what should be do after reading
                                           the rule *)
  acts  : 'a;                           (* action to produce the final 'c. either
                                           ('b -> 'c) or ('x -> 'b -> 'c) pos *)
  rest  : 'b rule;                      (* remaining to parse, will produce 'b *)
  full  : 'c rule;                      (* full rule. rest is a suffix of full.
                                           only use as a reference *)
  mutable read  : bool;                 (* to avoid lecture twice *)
  }

(* next element of an earley stack *)
and (_,_) element =
  (* cons cell of the stack *)
  | C : (('a -> 'b -> 'c) res pos, 'b, 'c, 'r) cell -> ('a,'r) element
  (* end of the stack *)
  | B : ('a -> 'b) res pos -> ('a,'b) element

(* head of the stack *)
type _ final = D : (('b -> 'c) res, 'b, 'c, 'r) cell -> 'r final

(* INVARIANTS:

1° Consider two C elements (or two D elements) of a stack.  If their
   have the same debut, rest and full is means we have parsed the same
   prefix of the rule from debut to produce a value of the same type.

   Then, the two cell MUST HAVE PHYSICALLY EQUAL stack

2° For D nodes only, we keep only one for each (debut, rest, full) triple
   so acts are necessarily physically equal
*)

let eq_pos p1 p2 = match p1, p2 with
  | Some((buf,pos),_), Some((buf',pos'),_) -> buffer_equal buf buf' && pos = pos'
  | None, None -> true
  | _ -> false

let eq_D (D {debut; rest; full; stack; acts})
         (D {debut=d'; rest=r'; full=fu'; stack = stack'; acts=acts'}) =
  eq_pos debut d' && eq rest r' && eq full fu' && (assert (eq stack stack');
                                                   assert (eq acts acts'); true)

let eq_C c1 c2 = eq c1 c2 ||
  match c1, c2 with
    (C {debut; rest; full; stack; acts},
     C {debut=d'; rest=r'; full=fu'; stack = stack'; acts = acts'}) ->
      eq_pos debut d' && eq rest r' && eq full fu'
      && (assert (eq stack stack'); assert(eq acts acts'); true)
  | (B acts, B acts') -> assert (eq acts acts'); true
  | _ -> false

let idtCell = Container.create ()
let idtEmpty : type a.(a->a) rule = (Empty Idt,idtCell)


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
     (Next(i,name,NonTerm(i,ref g),Idt,idtEmpty), Container.create ())

let iter_rules : type a.(a rule -> unit) -> a rule list -> unit = List.iter

let force = Fixpoint.force

let empty = Fixpoint.from_val (true, Charset.empty)
let any = Fixpoint.from_val (true, Charset.full)

let pre_rule (x,_) = x

(* managment of info = accept empty + charset accepted as first char *)
let rec rule_info:type a.a rule -> info Fixpoint.t = fun r ->
  match pre_rule r with
  | Next(i,_,_,_,_) -> i
  | Empty _ -> empty
  | Dep(_) -> any

let symbol_info:type a.a symbol -> info Fixpoint.t  = function
  | Term(i,_) -> Fixpoint.from_val (false,i)
  | NonTerm(i,_) | Greedy(i,_) -> i
  | Test(set,_) -> Fixpoint.from_val (true, set)

let compose_info i1 i2 =
  let i1 = symbol_info i1 in
  match pre_rule i2 with
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
    match pre_rule rule with
    | Next(_,name,_,_,rs) -> Printf.fprintf ch "%s %a" name print_rule rs
    | Dep _ -> Printf.fprintf ch "DEP"
    | Empty _ -> ()

let print_pos ch (buf, pos) =
  Printf.fprintf ch "%d:%d" (line_num buf) pos

let print_final ch (D {rest; full}) =
  let rec fn : type a.a rule -> unit = fun rule ->
    if eq rule rest then Printf.fprintf ch "* " ;
    match pre_rule rule with
    | Next(_,name,_,_,rs) -> Printf.fprintf ch "%s " name; fn rs
    | Dep _ -> Printf.fprintf ch "DEP"
    | Empty _ -> ()
  in
  fn full;
  let (ae,set) = force (rule_info rest) in
  if !debug_lvl > 0 then Printf.fprintf ch "(%a %b)" Charset.print set ae

let print_element : type a b.out_channel -> (a,b) element -> unit = fun ch el ->
  let rec fn : type a b.a rule -> b rule -> unit = fun rest rule ->
    if eq rule rest then Printf.fprintf ch "* " ;
    match pre_rule rule with
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
type _ dep_pair = P : 'a rule * ('a, 'b) element list ref * (('a, 'b) element -> unit) list ref -> 'b dep_pair

type 'b dep_pair_tbl = 'b dep_pair Container.table

let hook_assq : type a b. a rule -> b dep_pair_tbl -> ((a, b) element -> unit) -> unit =
  fun r dlr f ->
    try match Container.find dlr (snd r) with
      P(r',ptr,g) ->
        match r === r' with
        | Eq -> g := f::!g; List.iter f !ptr;
        | _ -> assert false
    with Not_found ->
      Container.add dlr (snd r) (P(r,ref [], ref [f]))

(* ajout d'un element dans une pile *)
let add_assq : type a b. a rule -> (a, b) element  -> b dep_pair_tbl -> (a, b) element list ref =
  fun r el dlr ->
    try match Container.find dlr (snd r) with
      P(r',stack,g) ->
        match r === r' with
        | Eq ->
           if not (List.exists (eq_C el) !stack) then (
             if !debug_lvl > 3 then
               Printf.eprintf "add stack %a ==> %a\n%!" print_rule r print_element el;
             stack := el :: !stack; List.iter (fun f -> f el) !g); stack
        | _ -> assert false
    with Not_found ->
      if !debug_lvl > 3 then
        Printf.eprintf "new stack %a ==> %a\n%!" print_rule r print_element el;
      let res = ref [el] in Container.add dlr (snd r) (P(r,res, ref [])) ; res

let find_assq : type a b. a rule -> b dep_pair_tbl -> (a, b) element list ref =
  fun r dlr ->
    try match Container.find dlr (snd r) with
      P(r',stack,g) ->
        match r === r' with
        | Eq -> stack
        | _ -> assert false
    with Not_found ->
      let res = ref [] in Container.add dlr (snd r) (P(r,res, ref [])); res

let debut pos = function D { debut } -> match debut with None -> pos | Some (p,_) -> p

type 'a pos_tbl = (int * int, 'a final list) Hashtbl.t

let find_pos_tbl t (buf,pos) = Hashtbl.find t (buffer_uid buf, pos)
let add_pos_tbl t (buf,pos) v = Hashtbl.replace t (buffer_uid buf, pos) v
let char_pos (buf,pos) = line_offset buf + pos
let elt_pos pos el = char_pos (debut pos el)

(* ajoute un élément dans la table et retourne true si il est nouveau *)
let add : string -> position -> 'a final -> 'a pos_tbl -> bool =
  fun info pos_final element elements ->
    let deb = debut pos_final element in
    let oldl = try find_pos_tbl elements deb with Not_found -> [] in
    let rec fn = function
      | [] ->
         if !debug_lvl > 1 then Printf.eprintf "add %s %a %d %d\n%!" info print_final element
           (char_pos deb) (char_pos pos_final);
        add_pos_tbl elements deb (element :: oldl); true
      | e::es ->
         (match e, element with
           D {debut=d; rest; full; stack; acts},
           D {debut=d'; rest=r'; full=fu'; stack = stack'; acts = acts'}
         ->
(*         if !debug_lvl > 2 then Printf.eprintf "comparing %s %a %a %d %d %b %b %b %a %a\n%!"
            info print_final e print_final element (elt_pos pos_final e) (elt_pos pos_final element) (eq_pos d d')
           (eq rest r') (eq full fu') print_res acts print_res acts';*)
         (match
           eq_pos d d', rest === r', full === fu', acts, acts' with
           | true, Eq, Eq, act, acts' ->
              if not (eq_res acts acts') && !warn_merge then
                Printf.eprintf "\027[31mmerging %a %a %a [%s]\027[0m\n%!"
                  print_final element print_pos (debut pos_final element)
                  print_pos pos_final (filename (fst pos_final));
              assert(stack == stack' ||
                       (Printf.eprintf "\027[31mshould be the same stack %s %a %d %d\027[0m\n%!"
                          info print_final element (elt_pos pos_final element)
                          (char_pos pos_final); false));
              false
          | _ ->
            fn es))
    in fn oldl

let taille : 'a final -> (Obj.t, Obj.t) element list ref -> int = fun el adone ->
  let cast_elements : type a b.(a,b) element list -> (Obj.t, Obj.t) element list = Obj.magic in
  let res = ref 1 in
  let rec fn : (Obj.t, Obj.t) element list -> unit = fun els ->
    List.iter (fun el ->
      if List.exists (eq el) !adone then () else begin
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

let protect errpos f a = try f a with Error -> ()

let protect_cons errpos f a acc = try f a :: acc with Error -> acc

let combine2 : type a0 a1 a2 b bb c.(a2 -> b) res -> (b -> c) res pos -> (a1 -> a2) pos -> (a0 -> a1) pos -> (a0 -> c) res pos =
  fun acts acts' g f ->
    pos_apply3 (fun acts' g f ->
        cps(sin f,cps(sin g,cps(acts,acts')))
      ) acts' g f

let combine1 : type a b c d.(c -> d) res -> (a -> b) pos -> (a -> (b -> c) -> d) res pos =
  fun acts g ->
    match acts, g with
    | _ -> pos_apply (fun g -> Csp(sin g,acts)) g

(* phase de lecture d'un caractère, qui ne dépend pas de la bnf *)
let lecture : type a.errpos -> blank -> int -> position -> position -> a pos_tbl -> a final buf_table -> a final buf_table =
  fun errpos blank id pos pos_ab elements tbl ->
    if !debug_lvl > 3 then Printf.eprintf "read at line = %d col = %d (%d)\n%!" (line_num (fst pos)) (snd pos) id;
    if !debug_lvl > 2 then Printf.eprintf "read after blank line = %d col = %d (%d)\n%!" (line_num (fst pos_ab)) (snd pos_ab) id;
    let tbl = ref tbl in
    Hashtbl.iter (fun _ l -> List.iter (function
    | D ({debut; stack;acts; rest; full; read} as r) as element ->
       if not read then match pre_rule rest with
       | Next(_,_,Term (_,f),g,rest) ->
          (try
             r.read <- true;
             (*Printf.eprintf "lecture at %d %d\n%!" (line_num buf0) pos0;*)
             let debut = first_pos debut (Some(pos,pos_ab)) in
             let buf0, pos0 = pos_ab in
             let a, buf, pos = f buf0 pos0 in
             if !debug_lvl > 1 then
               Printf.eprintf "action for terminal of %a =>" print_final element;
             let a = try apply_pos g (buf0, pos0) (buf, pos) a
               with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
             if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
             let state =
               (D {debut; stack; acts = cns(Sin a,acts); rest; full; read = false})
             in
             tbl := insert_buf buf pos state !tbl
           with Error -> ())

       | Next(_,_,Greedy(_,f),g,rest) ->
          (try
             r.read <- true;
             let debut = first_pos debut (Some(pos,pos_ab)) in
             let buf0, pos0 = pos_ab in
             if !debug_lvl > 0 then Printf.eprintf "greedy at %d %d\n%!" (line_num buf0) pos0;
             let a, buf, pos = f errpos blank (fst pos) (snd pos) buf0 pos0 in
             if !debug_lvl > 1 then
               Printf.eprintf "action for greedy of %a =>" print_final element;
             let a = try apply_pos g (buf0, pos0) (buf, pos) a
               with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
             if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
             let state =
               (D {debut; stack; acts = cns(Sin a,acts); rest; full; read = false})
             in
             tbl := insert_buf buf pos state !tbl
           with Error -> ())

       | Next(_,_,Test(s,f),g,rest) ->
          (try
             r.read <- true;
             let (buf0, pos0 as j) = pos_ab in
             if !debug_lvl > 1 then Printf.eprintf "testing at %d %d\n%!" (line_num buf0) pos0;
             let (a,b) = f (fst pos) (snd pos) buf0 pos0 in
             if b then begin
                 if !debug_lvl > 1 then Printf.eprintf "test passed\n%!";
                 let x = apply_pos g j j a in
                 let state = D {debut; stack; rest; full; acts = cns(Sin x,acts); read = false} in
                 tbl := insert_buf (fst pos) (snd pos) state !tbl
               end
           with Error -> ())
       | _ -> ()) l) elements;
    !tbl

(* selectionnne les éléments commençant par un terminal
   ayant la règle donnée *)
type 'b action = { a : 'a.'a rule -> ('a, 'b) element list ref -> unit }

let taille_tables els forward =
  let adone = ref [] in
  let res = ref 0 in
  Hashtbl.iter (fun _ els -> List.iter (fun el -> res := !res + 1 + taille el adone) els) els;
  iter_buf forward (fun el -> res := !res + 1 + taille el adone);
  !res

let good c i =
  let (ae,set) = force i in
  if !debug_lvl > 4 then Printf.eprintf "good %c %b %a" c ae Charset.print set;
  let res = ae || Charset.mem set c in
  if !debug_lvl > 4 then Printf.eprintf " => %b\n%!" res;
  res


(* fait toutes les prédictions et productions pour un element donné et
   comme une prédiction ou une production peut en entraîner d'autres,
   c'est une fonction récursive *)
let rec one_prediction_production
 : type a. errpos -> a final -> a pos_tbl -> a dep_pair_tbl -> position -> position -> char -> char ->  unit
 = fun errpos element0 elements dlr pos pos_ab c c' ->
   match element0 with
  (* prediction (pos, i, ... o NonTerm name::rest_rule) dans la table *)
   | D ({debut; acts; stack; rest; full; read} as r) ->

     if !debug_lvl > 1 then Printf.eprintf "predict/product for %a (%C %C)\n%!" print_final element0 c c';
     if not read then match pre_rule rest with
     | Next(info,_,(NonTerm(_,{contents = rules})),f,rest2) when good c info ->
        r.read <- true;
        let act =
          { a = (fun rule stack ->
            if good c (rule_info rule) then (
              let nouveau = D {debut=None; acts = Nil; stack; rest = rule; full = rule; read = false} in
              let b = add "P" pos nouveau elements in
              if b then one_prediction_production errpos nouveau elements dlr pos pos_ab c c'))
          }
        in
        let f = fix_begin f pos_ab in
        begin match pre_rule rest2, debut with
        | Empty (g), Some(_,pos') ->
          let g = fix_begin g pos' in
          if !debug_lvl > 1 then Printf.eprintf "RIGHT RECURSION OPTIM %a\n%!" print_final element0;
          iter_rules (fun r ->
            let complete = protect errpos (function
              | C {rest=rest2; acts=acts'; full; debut=d; stack} ->
                 let debut = first_pos d debut in
                 let c = C {rest=rest2; acts=combine2 acts acts' g f; full; debut; stack; read = false} in
                 ignore(add_assq r c dlr)
              | B acts' ->
                 let c = B (combine2 acts acts' g f) in
                 ignore (add_assq r c dlr))
            in
            assert (!stack <> []);
            List.iter complete !stack;
            act.a r (find_assq r dlr)) rules
        | _ ->
           let c = C {rest=rest2; acts=combine1 acts f; full; debut; stack; read = false} in
           iter_rules (fun r -> act.a r (add_assq r c dlr)) rules
        end
     | Dep(rule) ->
        r.read <- true;
        if !debug_lvl > 1 then Printf.eprintf "dependant rule\n%!";
       let a =
         let a = ref None in
         try let _ = apply acts (Sin (fun x -> a := Some x; raise Exit)) in assert false
         with Exit ->
           match !a with None -> assert false | Some a -> a
       in
       let cc = C { debut;
                    acts = Simple (Sin (fun b f -> f (eval (apply acts (Sin (fun _ -> b)))))); stack;
                   rest = idtEmpty; full; read = false } in
       let rule = rule a in
       let stack' = add_assq rule cc dlr in
       let nouveau = D {debut; acts = Nil; stack = stack'; rest = rule; full = rule; read = false } in
       let b = add "P" pos nouveau elements in
       if b then one_prediction_production errpos nouveau elements dlr pos pos_ab c c'

     (* production      (pos, i, ... o ) dans la table *)
     | Empty(a) ->
        r.read <- true;
        (try
           if !debug_lvl > 1 then
             Printf.eprintf "action for completion of %a: (%a x)=>" print_final element0
               print_res acts;
           let x = try apply acts (Sin (apply_pos_debut a debut pos pos_ab))
                   with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
           if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
          let complete = fun element ->
            match element with
            | C {debut=d; stack=els'; acts; rest; full} ->
               if good c (rule_info rest) then begin
                 if !debug_lvl > 1 then
                   Printf.eprintf "action for completion bis of %a: (%a x) =>" print_final element0 print_res (apply_pos_debut acts debut pos pos_ab);
                 let debut = first_pos d debut in
                 let acts =
                   try apply (apply_pos_debut acts debut pos pos_ab) x
                   with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e
                 in
                 if !debug_lvl > 1 then Printf.eprintf "succes %a\n%!" print_res acts;
                 let nouveau = D {debut; acts; stack=els'; rest; full; read = false } in
                 let b = add "C" pos nouveau elements in
                 if b then one_prediction_production errpos nouveau elements dlr pos pos_ab c c'
               end
            | B _ -> ()
          in
          let complete = protect errpos complete in
          if debut = None then hook_assq full dlr complete
          else List.iter complete !stack;
         with Error -> ())

     | _ -> ()

exception Parse_error of Input.buffer * int * string list

let count = ref 0

let parse_buffer_aux : type a.errpos -> bool -> bool -> a grammar -> blank -> buffer -> int -> a * buffer * int =
  fun errpos internal blank_after main blank buf0 pos0 ->
    let parse_id = incr count; !count in
    (* construction de la table initiale *)
    let elements : a pos_tbl = Hashtbl.create 31 in
    let r0 : a rule = grammar_to_rule main in
    let s0 : (a, a) element list ref = ref [B (Simple Nil)] in
    let init = D {debut=None; acts = Nil; stack=s0; rest=r0; full=r0; read = false } in
    let pos = ref pos0 and buf = ref buf0 in
    let pos' = ref pos0 and buf' = ref buf0 in
    let last_success = ref [] in
    let forward = ref empty_buf in
    if !debug_lvl > 0 then Printf.eprintf "entering parsing %d at line = %d(%d), col = %d(%d)\n%!"
      parse_id (line_num !buf) (line_num !buf') !pos !pos';
    let dlr = Container.create_table () in
    let prediction_production advance msg l =
      if advance then begin
          Hashtbl.clear elements;
          let buf'', pos'' = blank !buf !pos in
          buf' := buf''; pos' := pos'';
          update_errpos errpos (!buf', !pos');
        end;
      let c,_,_ = Input.read !buf' !pos' in
      let c',_,_ = Input.read !buf !pos in
      if !debug_lvl > 0 then Printf.eprintf "parsing %d: line = %d(%d), col = %d(%d), char = %C(%C)\n%!" parse_id (line_num !buf) (line_num !buf') !pos !pos' c c';
      List.iter (fun s ->
        if add msg (!buf,!pos) s elements then
          one_prediction_production errpos s elements dlr (!buf,!pos) (!buf',!pos') c c') l;
      if internal then begin
        try
          let found = ref false in
          List.iter (function D {stack=s1; rest=(Empty f,_); acts; full=r1} as elt ->
            if eq r0 r1 then (
              if not !found then last_success := ((!buf,!pos,!buf',!pos'), []) :: !last_success;
              found := true;
              assert (!last_success <> []);
              let (pos, l) = List.hd !last_success in
              last_success := (pos, (elt :: l)) :: List.tl !last_success)
          | _ -> ())
            l
        with Not_found -> ()
      end;
    in

    prediction_production true "I" [init];

    (* boucle principale *)
    let continue = ref true in
    while !continue do
      if !debug_lvl > 0 then Printf.eprintf "parse_id = %d, line = %d(%d), pos = %d(%d), taille =%d (%d,%d)\n%!"
        parse_id (line_num !buf) (line_num !buf') !pos !pos' (taille_tables elements !forward)
        (line_num (fst errpos.position)) (snd errpos.position);
      forward := lecture errpos blank parse_id (!buf, !pos) (!buf', !pos') elements !forward;
     let advance, l =
       try
         let (buf', pos', l, forward') = pop_firsts_buf !forward in
         let advance = not (buffer_equal !buf buf' && !pos = pos') in
         if advance then (
           pos := pos';
           buf := buf';
           Container.reset dlr; (* reset stack memo only if lecture makes progress.
                          this now allows for terminal parsing no input ! *));
         forward := forward';
         (advance, l)
       with Not_found -> (false, [])
     in
     if l = [] then continue := false else prediction_production advance "L" l;
    done;
    Container.reset dlr; (* don't forget final cleaning of assoc cell !! *)
    (* useless but clean *)
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
    let rec fn : type a.a final list -> a = function
      | [] -> raise Not_found
      | D {stack=s1; rest=(Empty f,_); acts; full=r1} :: els when eq r0 r1 ->
         (try
           let x = apply acts (Sin (apply_pos f (buf0, pos0) (!buf, !pos))) in
           let rec gn : type a b.(unit -> a) -> b res -> (b,a) element list -> a =
             fun cont x -> function
             | B (ls)::l ->
               (try eval (apply (apply_pos ls (buf0, pos0) (!buf, !pos)) x)
                with Error -> gn cont x l)
             | C _:: l ->
                gn cont x l
             | [] -> cont ()
           in
           gn (fun () -> fn els) x !s1
          with Error -> fn els)
      | _ :: els -> fn els
    in
    let a, buf, pos as result =
      if internal then
        let rec kn = function
          | [] -> parse_error ()
          | ((b,p,b',p'), elts) :: rest ->
             try
               let a = fn elts in
               if blank_after then (a, b', p') else (a, b, p)
             with
               Not_found -> kn rest
        in kn !last_success
      else
        try
          let a = fn (find_pos_tbl elements (buf0,pos0)) in
          if blank_after then (a, !buf', !pos') else (a, !buf, !pos)
        with Not_found -> parse_error ()
    in
    if !debug_lvl > 0 then
      Printf.eprintf "exit parsing %d at line = %d, col = %d\n%!" parse_id (line_num buf) pos;
    result

let internal_parse_buffer : type a.errpos -> a grammar -> blank -> ?blank_after:bool -> buffer -> int -> a * buffer * int
   = fun errpos g bl ?(blank_after=false) buf pos ->
       parse_buffer_aux errpos true blank_after g bl buf pos
