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

let _ = Printexc.record_backtrace true

(* Flags. *)
let debug_lvl  = ref 0
let warn_merge = ref true

(* Custom hash table module. [Hashtbl] won't  do  because  it  does  not
   accept keys that contain closures. Here a custom  comparing  function
   can be provided at the creation of the hash table. *)
module EqHashtbl :
  sig
    type ('a, 'b) t

    val create : ?equal:('a -> 'a -> bool) -> int -> ('a, 'b) t
    val add    : ('a, 'b) t -> 'a -> 'b -> unit
    val find   : ('a, 'b) t -> 'a -> 'b
    val iter   : ('a -> 'b -> unit) -> ('a, 'b) t -> unit
  end =
  struct
    type ('a, 'b) t =
      { equal              : 'a -> 'a -> bool
      ; mutable nb_buckets : int
      ; mutable buckets    : ('a * 'b) list array
      ; mutable max_size   : int
      ; mutable size_limit : int }

    let rec log2 n = if n <= 0 then 0 else 1 + log2 (n lsr 1)

    let create : ?equal:('a -> 'a -> bool) -> int -> ('a, 'b) t =
      fun ?(equal=(=)) nb_buckets ->
        let nb_buckets = max nb_buckets 8 in
        let buckets = Array.make nb_buckets [] in
        let size_limit = log2 nb_buckets + 7 in
        { equal ; nb_buckets ; buckets ; max_size = 0 ; size_limit }

    let iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit =
      fun fn h ->
        Array.iter (List.iter (fun (k,v) -> fn k v)) h.buckets

    let hash = Hashtbl.hash

    let find_bucket : ('a, 'b) t -> 'a -> int =
      fun h k -> hash k mod h.nb_buckets

    exception Size_is of int
    let rec add : ('a, 'b) t -> 'a -> 'b -> unit =
      fun h k v ->
        let i = find_bucket h k in
        let rec remove sz = function
          | []                             -> raise (Size_is sz)
          | (kv,_) :: ls when h.equal k kv -> ls
          | e      :: ls                   -> e :: remove (sz+1) ls
        in
        try h.buckets.(i) <- (k,v) :: remove 0 h.buckets.(i)
        with Size_is(sz) ->
          h.buckets.(i) <- (k,v) :: h.buckets.(i);
          h.max_size <- max h.max_size sz;
          if h.max_size > h.size_limit then grow h

    and grow : ('a, 'b) t -> unit =
      fun h ->
        let old_tbl = h.buckets in
        h.nb_buckets <- h.nb_buckets * 2;
        h.buckets <- Array.make h.nb_buckets [];
        h.size_limit <- h.size_limit + 1;
        h.max_size <- 0;
        Array.iter (List.iter (fun (k,v) -> add h k v)) old_tbl

    let find : ('a, 'b) t -> 'a -> 'b =
      fun h k ->
        let i = find_bucket h k in
        let rec find = function
          | []         -> raise Not_found
          | (kv,v)::xs -> if h.equal k kv then v else find xs
        in
        find h.buckets.(i)
  end

(* Comparison function accepting to compare everything. Be careful as it
   compares everything containing a closure with physical equality  only
   (even if closure appear deep in the compared structure). *)
let closure_eq x y = try x = y with _ -> x == y

module Fixpoint :
  sig
    type 'a t

    val from_val  : 'a -> 'a t
    val from_fun  : 'a t -> ('a -> 'a) -> 'a t
    val from_fun2 : 'a t -> 'a t -> ('a -> 'a -> 'a) -> 'a t
    val from_funl : 'a t list -> 'a -> ('a -> 'a -> 'a) -> 'a t
    val from_ref  : 'b ref -> ('b -> 'a t) -> 'a t
    val update    : 'a t -> unit
    val force     : 'a t -> 'a
  end =
  struct
    module rec H :
      sig
        type 'a fix =
          { mutable value  : 'a
          ; compute        : unit -> unit
          ; mutable deps   : W.t option
          ; mutable is_ref : ('a fix * (unit -> 'a fix)) option
          ; ident          : int }

        include Hashtbl.HashedType with type t = Obj.t fix
      end =
      struct
        type 'a fix =
          { mutable value  : 'a
          ; compute        : unit -> unit
          ; mutable deps   : W.t option
          ; mutable is_ref : ('a fix * (unit -> 'a fix)) option
          ; ident          : int }

        type t = Obj.t fix

        let equal a b = a.ident = b.ident

        let hash a = a.ident
      end
    and W : Weak.S with type data = H.t = Weak.Make(H)

    open H
    type 'a t = 'a fix

    let force : 'a t -> 'a = fun b -> b.value

    let new_id =
      let r = ref 0 in
      (fun () -> let x = !r in r := x + 1; x)

    let add_deps r {deps} =
      match deps with
      | None     -> true
      | Some tbl ->
          let r = Obj.magic r in
          if not (W.mem tbl r) then
            begin
              W.add tbl r;
              if !debug_lvl > 2 then
                Printf.eprintf "New rule (count = %d)\n%!" (W.count tbl)
            end;
          false

    let iter_deps fn {deps} =
      match deps with
      | None     -> ()
      | Some tbl -> W.iter (fun v -> fn (Obj.magic v)) tbl

    let from_val value =
      { value
      ; compute = ignore
      ; deps    = None
      ; is_ref  = None
      ; ident   = new_id () }

    let from_fun l fn =
      let rec res =
        { value   = fn l.value
        ; compute = (fun () -> res.value <- fn l.value)
        ; deps    = Some (W.create 31)
        ; is_ref  = None
        ; ident   = new_id () }
      in
      if add_deps res l then res.deps <- None;
      res

    let from_fun2 l1 l2 fn =
      let rec res =
        { value   = fn l1.value l2.value
        ; compute = (fun () -> res.value <- fn l1.value l2.value)
        ; deps    = Some (W.create 31)
        ; is_ref  = None
        ; ident   = new_id () }
      in
      let b1 = add_deps res l1 in
      let b2 = add_deps res l2 in
      if b1 && b2 then res.deps <- None;
      res

    let rec fold l a f =
      match l with
      | []   -> a
      | x::l -> fold l (f a x.value) f

    let from_funl l a fn =
      let rec res =
        { value   = fold l a fn
        ; compute = (fun () -> res.value <- fold l a fn)
        ; deps    = Some (W.create 31)
        ; is_ref  = None
        ; ident   = new_id () }
      in
      let fn acc x = add_deps res x && acc in
      if List.fold_left fn true l then res.deps <- None;
      res

    let from_ref l fn =
      let a = fn !l in
      let rec res =
        { value   = a.value
        ; compute = (fun () -> res.value <- (fn !l).value)
        ; deps    = Some (W.create 31)
        ; is_ref  = Some (a, fun () -> fn !l)
        ; ident   = new_id () }
      in
      ignore (add_deps res a);
      res

    let update b =
      begin
        match b.is_ref with
        | None      -> invalid_arg "Fixpoint.update";
        | Some(a,f) ->
            let a' = f () in
            ignore (add_deps b a');
            b.is_ref <- Some (a', f)
      end;
      let rec fn x =
        let old = x.value in x.compute ();
        if old <> x.value then iter_deps fn x
      in fn b
  end

type ('a,'b) eq  = Eq : ('a, 'a) eq | Neq : ('a, 'b) eq

let (===) : type a b.a -> b -> (a,b) eq = fun r1 r2 ->
  let open Obj in
  (* if not (is_block (repr r1) && is_block (repr r2)) then
     invalid_arg "block only for ===";*) (* FIXME *)
  if repr r1 == repr r2 then magic Eq else Neq

module Container : sig
  type t
  type 'a table

  val create : unit -> t
  val add : 'a table -> t -> 'a -> unit
  val find : 'a table -> t -> 'a
  val reset : 'a table -> unit
  val create_table : unit -> 'a table

end = struct

  type clist =
    | Cons : 'a table * 'a * clist -> clist
    | Nil  : clist

  and t = clist ref

  and 'a table = 'a option * clist ref list ref

  let create () : t = ref Nil

  let create_table : type a.a option -> a table = fun a -> (a, ref [])

  let add : type a. a table -> t -> a -> unit = fun t c a ->
    if List.memq c !(snd t) then (
      let rec fn = function
        | Nil -> assert false
        | Cons(t',x,r) ->
           match t === t' with
           | Eq -> Cons(t',a,r)
           | Neq -> Cons(t',x,fn r)
      in c:= fn !c
    ) else (
      c := Cons(t,a,!c);
      snd t := c :: !(snd t))

   let rec find_aux : type a. a table -> clist -> a = fun t c ->
     match c with
     | Nil -> raise Not_found
     | Cons(t',x,r) ->
        match t === t' with
        | Eq  -> x
        | Neq -> find_aux t r

   let find : type a. a table -> t -> a = fun t c -> find_aux t !c

   let reset : type a. a table -> unit = fun t ->
     let rec fn = function
       | Nil -> invalid_arg "reset"
       | Cons(t',x,r) ->
          match t === t' with Eq -> r | Neq -> Cons(t',x,fn r)
     in
     List.iter (fun l -> l := fn !l) !(snd t);
     snd t := []

   let create_table : type a. unit -> a table = fun () -> create_table None

end

open Input

exception Error
let give_up () = raise Error

type blank = buffer -> int -> buffer * int

let no_blank str pos = str, pos

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

let pos_apply2 : type a b c.(a -> b -> c) -> a pos -> b pos -> c pos=
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
  | NonTerm : info Fixpoint.t * 'a rule list -> 'a symbol
  (** non terminal *)
  | RefTerm : info Fixpoint.t * 'a rule list ref -> 'a symbol
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
  debut : (position * position) option; (* position in the buffer, before and after blank *)
  stack : ('c, 'r) element list ref;    (* tree of stack of what should be do after reading
                                           the rule *)
  acts  : 'a;
  rest  : 'b rule;
  full  : 'c rule }

(* next element of an earley stack *)
and (_,_) element =
  (* cons cell of the stack *)
  | C : (('a -> 'b -> 'c) pos, 'b, 'c, 'r) cell -> ('a,'r) element
  (* end of the stack *)
  | B : ('a -> 'b) pos -> ('a,'b) element

(* tête de pile de earley *)
type _ final = D : (('b -> 'c), 'b, 'c, 'r) cell -> 'r final

(* si t : table et t.(j) = (i, R, R' R) cela veut dire qu'entre i et j on a parsé
   la règle R' et qu'il reste R à parser. On a donc toujours
   i <= j et R suffix de R' R (c'est pour ça que j'ai écris R' R)
*)


(* a comparison for closure, that is a bit stronger than == *)
(* TODO: check if === is not as good *)
let eq_closure : type a b. a -> b -> bool =
  fun f g ->
    let open Obj in
    (*repr f == repr g || (Marshal.to_string f [Closures] = Marshal.to_string g [Closures])*)
    let adone = ref [] in
    let rec fneq f g =
      f == g ||
        match is_int f, is_int g with
        | true, true -> f = g
        | false, true | true, false -> false
        | false, false ->
           (*      if !debug_lvl > 10 then Printf.eprintf "*%!";*)
           let ft = tag f and gt = tag g in
           if ft = forward_tag then (
             (*      if !debug_lvl > 10 then Printf.eprintf "#%!";*)
             fneq (field f 0) g)
           else if gt = forward_tag then (
             (*      if !debug_lvl > 10 then Printf.eprintf "#%!";*)
             fneq f (field g 0))
           else if ft = custom_tag || gt = custom_tag then f = g
           else if ft <> gt then false
           else ((*if !debug_lvl > 10 then Printf.eprintf " %d %!" ft;*)
           if ft = string_tag || ft = double_tag || ft = double_array_tag then f = g
           else if ft = abstract_tag || ft = out_of_heap_tag || ft = no_scan_tag then f == g
           else if ft =  infix_tag then (
             Printf.eprintf "INFIX TAG\n%!"; (* FIXME *)
             assert false;)
           else
               size f == size g &&
               let rec gn i =
                 if i < 0 then true
                 else fneq (field f i) (field g i) && gn (i - 1)
               in
               List.exists (fun (f',g') -> f == f' && g == g') !adone ||
                (List.for_all (fun (f',g') -> f != f' && g != g') !adone &&
                 (adone := (f,g)::!adone;
                  let r = gn (size f - 1) in
                  r)))

    in fneq (repr f) (repr g)

let eq : 'a 'b.'a -> 'b -> bool = fun x y -> (x === y) <> Neq

let eq_pos p1 p2 = match p1, p2 with
  | Some((buf,pos),_), Some((buf',pos'),_) -> buffer_equal buf buf' && pos = pos'
  | None, None -> true
  | _ -> false


let eq_D (D {debut; rest; full; stack})
         (D {debut=d'; rest=r'; full=fu'; stack = stack'}) =
  eq_pos debut d' && eq rest r' && eq full fu' && (assert (eq stack stack'); true)

let eq_C c1 c2 = eq c1 c2 ||
  match c1, c2 with
    (C {debut; rest; full; stack; acts},
     C {debut=d'; rest=r'; full=fu'; stack = stack'; acts = acts'}) ->
      eq_pos debut d' && eq rest r' && eq full fu'
      && (assert (eq stack stack'); eq_closure acts acts')
  | (B acts, B acts') -> eq_closure acts acts'
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
     (Next(i,name,NonTerm(i,g),Idt,idtEmpty), Container.create ())

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
  | NonTerm(i,_) | Greedy(i,_) | RefTerm(i,_) -> i
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
type _ dep_pair = P : 'a rule * ('a, 'b) element list ref * (('a, 'b) element -> unit) ref -> 'b dep_pair

type 'b dep_pair_tbl = 'b dep_pair Container.table

let hook_assq : type a b. a rule -> b dep_pair_tbl -> ((a, b) element -> unit) -> unit =
  fun r dlr f ->
    try match Container.find dlr (snd r) with
      P(r',ptr,g) ->
        match r === r' with
        | Eq -> g := (let g = !g in (fun el -> f el; g el)); List.iter f !ptr;
        | _ -> assert false
    with Not_found ->
      Container.add dlr (snd r) (P(r,ref [], ref f))

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
             stack := el :: !stack; !g el); stack
        | _ -> assert false
    with Not_found ->
      if !debug_lvl > 3 then
        Printf.eprintf "new stack %a ==> %a\n%!" print_rule r print_element el;
      let res = ref [el] in Container.add dlr (snd r) (P(r,res, ref (fun el -> ()))) ; res

let find_assq : type a b. a rule -> b dep_pair_tbl -> (a, b) element list ref =
  fun r dlr ->
    try match Container.find dlr (snd r) with
      P(r',stack,g) ->
        match r === r' with
        | Eq -> stack
        | _ -> assert false
    with Not_found ->
      let res = ref [] in Container.add dlr (snd r) (P(r,res, ref (fun el -> ()))); res

let debut pos = function D { debut } -> match debut with None -> pos | Some (p,_) -> p

type 'a pos_tbl = (int * int, 'a final list) Hashtbl.t

let find_pos_tbl t (buf,pos) = Hashtbl.find t (buffer_uid buf, pos)
let add_pos_tbl t (buf,pos) v = Hashtbl.replace t (buffer_uid buf, pos) v
let char_pos (buf,pos) = line_offset buf + pos
let elt_pos pos el = char_pos (debut pos el)

let merge_acts o n =
  let rec fnacts acc = function
    | [] -> acc
    | a::l -> if List.exists (eq_closure a) acc then fnacts acc l else fnacts (a::acc) l
  in fnacts o n

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
         (*if !debug_lvl > 3 then Printf.eprintf "comparing %s %a %a %d %d %b %b %b\n%!"
            info print_final e print_final element (elt_pos pos_final e) (elt_pos pos_final element) (eq_pos d d')
           (eq rest r') (eq full fu');*)
         (match
           eq_pos d d', rest === r', full === fu', acts, acts' with
           | true, Eq, Eq, act, acts' ->
              if not (eq_closure acts acts') && !warn_merge then
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

let combine2 : type a0 a1 a2 b bb c.(a2 -> b) -> (b -> c) pos -> (a1 -> a2) pos -> (a0 -> a1) pos -> (a0 -> c) pos =
   fun acts acts' g f ->
     compose acts' (pos_apply (fun g x -> acts (g x)) (compose g f))

let combine1 : type a b c d.(c -> d) -> (a -> b) pos -> (a -> (b -> c) -> d) pos =
   fun acts g -> pos_apply (fun g x -> let y = g x in fun h -> acts (h y)) g

(* phase de lecture d'un caractère, qui ne dépend pas de la bnf *)
let lecture : type a.errpos -> blank -> int -> position -> position -> a pos_tbl -> a final buf_table -> a final buf_table =
  fun errpos blank id pos pos_ab elements tbl ->
    if !debug_lvl > 3 then Printf.eprintf "read at line = %d col = %d (%d)\n%!" (line_num (fst pos)) (snd pos) id;
    if !debug_lvl > 2 then Printf.eprintf "read after blank line = %d col = %d (%d)\n%!" (line_num (fst pos_ab)) (snd pos_ab) id;
    let tbl = ref tbl in
    Hashtbl.iter (fun _ l -> List.iter (function
    | D {debut; stack;acts; rest; full} as element ->
       match pre_rule rest with
       | Next(_,_,Term (_,f),g,rest0) ->
          (try
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
               (D {debut; stack; acts = (fun f -> acts (f a)); rest=rest0; full;})
             in
             tbl := insert_buf buf pos state !tbl
           with Error -> ())

       | Next(_,_,Greedy(_,f),g,rest0) ->
          (try
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
               (D {debut; stack; acts = (fun f -> acts (f a)); rest=rest0; full;})
             in
             tbl := insert_buf buf pos state !tbl
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
   | D {debut; acts; stack; rest; full} ->

     if !debug_lvl > 1 then Printf.eprintf "predict/product for %a (%C %C)\n%!" print_final element0 c c';
     match pre_rule rest with
     | Next(info,_,(NonTerm (_,rules) | RefTerm(_,{contents = rules})),f,rest2) when good c info ->
        let act =
          { a = (fun rule stack ->
            if good c (rule_info rule) then (
              let nouveau = D {debut=None; acts = idt; stack; rest = rule; full = rule} in
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
                 let c = C {rest=rest2; acts=combine2 acts acts' g f; full; debut; stack} in
                 ignore(add_assq r c dlr)
              | B acts' ->
                 let c = B (combine2 acts acts' g f) in
                 ignore (add_assq r c dlr))
            in
            assert (!stack <> []);
            List.iter complete !stack;
            act.a r (find_assq r dlr)) rules
        | _ ->
           let c = C {rest=rest2; acts=combine1 acts f; full; debut; stack} in
           iter_rules (fun r -> act.a r (add_assq r c dlr)) rules
        end
     | Dep(r) ->
       if !debug_lvl > 1 then Printf.eprintf "dependant rule\n%!";
       let a =
         let a = ref None in
         try let _ = acts (fun x -> a := Some x; raise Exit) in assert false
         with Exit ->
           match !a with None -> assert false | Some a -> a
       in
       let cc = C { debut;  acts = Simple (fun b f -> f (acts (fun _ -> b))); stack;
                   rest = idtEmpty; full } in
       let rule = r a in
       let stack' = add_assq rule cc dlr in
       let nouveau = D {debut; acts = idt; stack = stack'; rest = rule; full = rule } in
       let b = add "P" pos nouveau elements in
       if b then one_prediction_production errpos nouveau elements dlr pos pos_ab c c'

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
            | C {debut=d; stack=els'; acts; rest; full} ->
               if good c (rule_info rest) then begin
                 if !debug_lvl > 1 then
                   Printf.eprintf "action for completion bis of %a =>" print_final element0;
                 let debut = first_pos d debut in
                 let x =
                   try apply_pos_debut acts debut pos pos_ab x
                   with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e
                 in
                 if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
                 let nouveau = D {debut; acts = x; stack=els'; rest; full } in
                 let b = add "C" pos nouveau elements in
                 if b then one_prediction_production errpos nouveau elements dlr pos pos_ab c c'
               end
            | B _ -> ()
          in
          let complete = protect errpos complete in
          if debut = None then hook_assq full dlr complete
          else List.iter complete !stack;
         with Error -> ())

     | Next(_,_,Test(s,f),g,rest) ->
        (try
          let j = pos_ab in
          if !debug_lvl > 1 then Printf.eprintf "testing at %d\n%!" (elt_pos pos element0);
          let (a,b) = f (fst pos) (snd pos) (fst j) (snd j) in
          if b then begin
            if !debug_lvl > 1 then Printf.eprintf "test passed\n%!";
            let nouveau = D {debut; stack; rest; full;
                             acts = let x = apply_pos g j j a in fun h -> acts (h x)} in
            let b = add "T" pos nouveau elements in
            if b then one_prediction_production errpos nouveau elements dlr  pos pos_ab c c'
          end
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
    let s0 : (a, a) element list ref = ref [B Idt] in
    let init = D {debut=None; acts = idt; stack=s0; rest=r0; full=r0 } in
    let pos = ref pos0 and buf = ref buf0 in
    let pos' = ref pos0 and buf' = ref buf0 in
    let last_success = ref [] in
    let forward = ref empty_buf in
    if !debug_lvl > 0 then Printf.eprintf "entering parsing %d at line = %d(%d), col = %d(%d)\n%!"
      parse_id (line_num !buf) (line_num !buf') !pos !pos';
    let dlr = Container.create_table () in
    let prediction_production msg l =
      Hashtbl.clear elements;
      let buf'', pos'' = blank !buf !pos in
      let c,_,_ = Input.read buf'' pos'' in
      let c',_,_ = Input.read !buf !pos in
      buf' := buf''; pos' := pos'';
      update_errpos errpos (buf'', pos'');
      if !debug_lvl > 0 then Printf.eprintf "parsing %d: line = %d(%d), col = %d(%d), char = %C(%C)\n%!" parse_id (line_num !buf) (line_num !buf') !pos !pos' c c';
      List.iter (fun s ->
        ignore (add msg (!buf,!pos) s elements);
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
            (find_pos_tbl elements (buf0,pos0))
        with Not_found -> ()
      end;
    in

    prediction_production "I" [init];

    (* boucle principale *)
    let continue = ref true in
    while !continue do
      if !debug_lvl > 0 then Printf.eprintf "parse_id = %d, line = %d(%d), pos = %d(%d), taille =%d (%d,%d)\n%!"
        parse_id (line_num !buf) (line_num !buf') !pos !pos' (taille_tables elements !forward)
        (line_num (fst errpos.position)) (snd errpos.position);
      forward := lecture errpos blank parse_id (!buf, !pos) (!buf', !pos') elements !forward;
     let l =
       try
         let (buf', pos', l, forward') = pop_firsts_buf !forward in
         if not (buffer_equal !buf buf' && !pos = pos') then (
           pos := pos';
           buf := buf';
           Container.reset dlr; (* reset stack memo only if lecture makes progress.
                          this now allows for terminal parsing no input ! *));
         forward := forward';
         l
       with Not_found -> []
     in
     if l = [] then continue := false else prediction_production "L" l;
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
           let x = acts (apply_pos f (buf0, pos0) (!buf, !pos)) in
           let rec gn : type a b.(unit -> a) -> b -> (b,a) element list -> a =
             fun cont x -> function
             | B (ls)::l ->
               (try apply_pos ls (buf0, pos0) (!buf, !pos) x
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

let partial_parse_buffer : type a.a grammar -> blank -> ?blank_after:bool -> buffer -> int -> a * buffer * int
   = fun g bl ?(blank_after=true) buf pos ->
       parse_buffer_aux (init_errpos buf pos) false blank_after g bl buf pos

let internal_parse_buffer : type a.errpos -> a grammar -> blank -> ?blank_after:bool -> buffer -> int -> a * buffer * int
   = fun errpos g bl ?(blank_after=false) buf pos ->
       parse_buffer_aux errpos true blank_after g bl buf pos

let solo = fun ?(name=new_name ()) ?(accept_empty=false) set s ->
  let j = Fixpoint.from_val (accept_empty,set) in
  (j, [(Next(j,name,Term (set, s),Idt,idtEmpty),Container.create ())])

let greedy_solo =
  fun ?(name=new_name ()) i s ->
    let cache = Hashtbl.create 101 in
    let s = fun ptr blank b p b' p' ->
      let key = (buffer_uid b, p, buffer_uid b', p') in
      let l = try Hashtbl.find cache key with Not_found -> [] in
      try
        let (_,_,r) = List.find (fun (p, bl, _) -> p == ptr && bl == blank) l in
        r
      with Not_found ->
        let r = s ptr blank b p b' p' in
        let l = (ptr,blank,r)::l in
        Hashtbl.replace cache key l;
        r
    in
    (i, [(Next(i,name,Greedy(i,s),Idt,idtEmpty),Container.create ())])

let test = fun ?(name=new_name ()) set f ->
  let i = (true,set) in
  let j = Fixpoint.from_val i in
  (j, [(Next(j,name,Test (set, (fun _ _ -> f)),Idt,idtEmpty),Container.create ())])

let blank_test = fun ?(name=new_name ()) set f ->
  let i = (true,set) in
  let j = Fixpoint.from_val i in
  (j, [(Next(j,name,Test (set, f),Idt,idtEmpty),Container.create ())])

let success_test a = test ~name:"SUCCESS" Charset.full (fun _ _ -> (a, true))

let with_blank_test a = blank_test ~name:"BLANK" Charset.full
  (fun buf' pos' buf pos -> (a, not (buffer_equal buf' buf) || pos' <> pos))

let no_blank_test a = blank_test ~name:"NOBLANK" Charset.full
  (fun buf' pos' buf pos -> (a, buffer_equal buf' buf && pos' = pos))

let nonterm (i,s) = NonTerm(i,s)

let next_aux name s f r = (Next(compose_info s r, name, s,f,r), Container.create ())

let next : type a b c. a grammar -> (a -> b) pos -> (b -> c) rule -> c rule =
  fun s f r -> match snd s with
  | [(Next(i,name,s0,g,(Empty h,_)),_)] ->
     next_aux name s0 (compose3 f h g) r
  | _ -> next_aux (new_name ()) (nonterm s) f r

let eof : 'a -> 'a grammar
  = fun a ->
    let fn buf pos =
      if is_empty buf pos then (a,buf,pos) else raise Error
    in
    solo (Charset.singleton '\255') fn

let mk_grammar s = (grammar_info s, s)

let give_name name (i,_ as g) =
  (i, [grammar_to_rule ~name g])

let apply : type a b. (a -> b) -> a grammar -> b grammar = fun f l1 ->
  mk_grammar [next l1 (Simple f) idtEmpty]

let apply_position : type a b. (a -> buffer -> int -> buffer -> int -> b) -> a grammar -> b grammar = fun f l1 ->
  mk_grammar [next l1 Idt (Empty(WithPos(fun b p b' p' a -> f a b p b' p')),Container.create ())]

let sequence : 'a grammar -> 'b grammar -> ('a -> 'b -> 'c) -> 'c grammar
  = fun l1 l2 f -> mk_grammar [next l1 Idt (next l2 (Simple (fun b a -> f a b)) idtEmpty)]

let sequence_position : 'a grammar -> 'b grammar -> ('a -> 'b -> buffer -> int -> buffer -> int -> 'c) -> 'c grammar
   = fun l1 l2 f ->
    mk_grammar [next l1 Idt (next l2 Idt (Empty(WithPos(fun b p b' p' a' a -> f a a' b p b' p')),Container.create ()))]

let parse_buffer : 'a grammar -> blank -> buffer -> 'a =
  fun g blank buf ->
    let g = sequence g (eof ()) (fun x _ -> x) in
    let (a, _, _) = partial_parse_buffer g blank buf 0 in
    a

let parse_string ?(filename="") grammar blank str =
  let str = Input.from_string ~filename str in
  parse_buffer grammar blank str

let parse_channel ?(filename="") grammar blank ic  =
  let str = Input.from_channel ~filename ic in
  parse_buffer grammar blank str

let parse_file grammar blank filename  =
  let str = Input.from_file filename in
  parse_buffer grammar blank str

module WithPP(PP : Preprocessor) =
  struct
    module InPP = Input.WithPP(PP)

    let parse_string ?(filename="") grammar blank str =
      let str = InPP.from_string ~filename str in
      parse_buffer grammar blank str

    let parse_channel ?(filename="") grammar blank ic  =
      let str = InPP.from_channel ~filename ic in
      parse_buffer grammar blank str

    let parse_file grammar blank filename  =
      let str = InPP.from_file filename in
      parse_buffer grammar blank str
  end

let fail : unit -> 'a grammar
  = fun () ->
    let fn buf pos = raise Error in
    solo Charset.empty fn

let error_message : (unit -> string) -> 'a grammar
  = fun msg ->
    (* compose with a test with a full charset to pass the final charset test in
       internal_parse_buffer *)
    let i = (false,Charset.full) in
    let j = Fixpoint.from_val i in
    let fn errpos blank _ _ buf pos =
      add_errmsg errpos buf pos msg;
      raise Error
    in
    (j, [(Next(j,"error",Greedy (j, fn),Idt,idtEmpty),Container.create ())])

let unset : string -> 'a grammar
  = fun msg ->
    let fn buf pos =
      failwith msg
    in
    solo Charset.empty fn (* make sure we have the message *)

let declare_grammar name =
  let g = snd (unset (name ^ " not set")) in
  let ptr = ref g in
  let j = Fixpoint.from_ref ptr grammar_info in
  mk_grammar [(Next(j,name,RefTerm (j, ptr),Idt, idtEmpty),Container.create ())]

let set_grammar : type a.a grammar -> a grammar -> unit = fun p1 p2 ->
  match snd p1 with
  | [(Next(_,name,RefTerm(i,ptr),f,e),_)] ->
     (match f === Idt, e === idtEmpty with
     | Eq, Eq -> ptr := snd p2; Fixpoint.update i;
     | _ -> invalid_arg "set_grammar")
  (*Printf.eprintf "setting %s %b %a\n%!" name ae Charset.print set;*)
  | _ -> invalid_arg "set_grammar"

let grammar_name : type a.a grammar -> string = fun p1 ->
  match snd p1 with
  | [(Next(_,name,_,_,(Empty _,_)),_)] -> name
  | _ -> new_name ()

let char : ?name:string -> char -> 'a -> 'a grammar
  = fun ?name c a ->
    let msg = Printf.sprintf "%C" c in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c', buf', pos' = read buf pos in
      if c = c' then (a,buf',pos') else give_up ()
    in
    solo ~name (Charset.singleton c) fn

let in_charset : ?name:string -> Charset.t -> char grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "[%s]" (Charset.show cs) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c, buf', pos' = read buf pos in
      if Charset.mem cs c then (c,buf',pos') else give_up ()
    in
    solo ~name cs fn

let not_in_charset : ?name:string -> Charset.t -> unit grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "^[%s]" (Charset.show cs) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c, buf', pos' = read buf pos in
      if Charset.mem cs c then ((), false) else ((), true)
    in
    test ~name (Charset.complement cs) fn

let blank_not_in_charset : ?name:string -> Charset.t -> unit grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "^[%s]" (Charset.show cs) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos _ _ =
      let c, buf', pos' = read buf pos in
      if Charset.mem cs c then ((), false) else ((), true)
    in
    blank_test ~name (Charset.complement cs) fn

let any : char grammar
  = let fn buf pos =
      let c, buf', pos' = read buf pos in
      if c = '\255' then give_up ();
      (c,buf',pos')
    in
    solo ~name:"ANY" Charset.(del full '\255') fn

let debug msg : unit grammar
    = let fn buf pos =
        Printf.eprintf "%s file:%s line:%d col:%d\n%!" msg (filename buf) (line_num buf) pos;
        ((), true)
      in
      test ~name:msg Charset.empty fn

let string : ?name:string -> string -> 'a -> 'a grammar
  = fun ?name s a ->
    let name = match name with None -> s | Some n -> n in
    let fn buf pos =
      let buf = ref buf in
      let pos = ref pos in
      let len_s = String.length s in
      for i = 0 to len_s - 1 do
        let c, buf', pos' = read !buf !pos in
        if c <> s.[i] then give_up ();
        buf := buf'; pos := pos'
      done;
      (a,!buf,!pos)
    in
    solo ~name ~accept_empty:(s="") (Charset.singleton s.[0]) fn

let option : 'a -> 'a grammar -> 'a grammar
  = fun a (_,l) -> mk_grammar ((Empty (Simple a),Container.create())::l)

let regexp : ?name:string -> string -> string array grammar =
  fun ?name str ->
    let name = match name with None -> String.escaped str | Some n -> n in
    let (re, grps) = Regexp.regexp_from_string str in
    let fn buf pos =
      let (buf, pos) = Regexp.read_regexp re buf pos in
      (Array.map (!) grps, buf, pos)
    in
    solo ~name ~accept_empty:(Regexp.accept_empty re)
      (Regexp.accepted_first_chars re) fn

let blank_regexp : string -> blank =
  fun str ->
    let (re, _) = Regexp.regexp_from_string str in
    Regexp.read_regexp re

(* charset is now useless ... will be suppressed soon *)
(*
let black_box : (buffer -> int -> 'a * buffer * int) -> Charset.t -> string -> 'a grammar
  = fun fn set name -> solo ~name set fn
*)
let black_box : (buffer -> int -> 'a * buffer * int) -> Charset.t -> bool -> string -> 'a grammar
  = fun fn set accept_empty name -> solo ~name ~accept_empty set fn

let empty : 'a -> 'a grammar = fun a -> (empty,[(Empty (Simple a), Container.create ())])

let sequence3 : 'a grammar -> 'b grammar -> 'c grammar -> ('a -> 'b -> 'c -> 'd) -> 'd grammar
  = fun l1 l2 l3 f ->
    sequence l1 (sequence l2 l3 (fun x y z -> f z x y)) (fun z f -> f z)

let fsequence : 'a grammar -> ('a -> 'b) grammar -> 'b grammar
  = fun l1 l2 -> mk_grammar [next l1 Idt (grammar_to_rule l2)]

let fsequence_position : 'a grammar -> ('a -> buffer -> int -> buffer -> int -> 'b) grammar -> 'b grammar
  = fun l1 l2 ->
    apply_position idt (fsequence l1 l2)

let conditional_sequence : 'a grammar -> ('a -> 'b) -> 'c grammar -> ('b -> 'c -> 'd) -> 'd grammar
  = fun l1 cond l2 f ->
    mk_grammar [next l1 (Simple cond) (next l2 (Simple (fun b a -> f a b)) idtEmpty)]

let conditional_sequence_position : 'a grammar -> ('a -> 'b) -> 'c grammar -> ('b -> 'c -> buffer -> int -> buffer -> int -> 'd) -> 'd grammar
   = fun l1 cond l2 f ->
     mk_grammar [next l1 (Simple cond)
                  (next l2 Idt (Empty(WithPos(fun b p b' p' a' a -> f a a' b p b' p')),Container.create ()))]

let conditional_fsequence : 'a grammar -> ('a -> 'b) -> ('b -> 'c) grammar -> 'c grammar
  = fun l1 cond l2 ->
    mk_grammar [next l1 (Simple cond) (grammar_to_rule l2)]

let conditional_fsequence_position : 'a grammar -> ('a -> 'b) -> ('b -> buffer -> int -> buffer -> int -> 'c) grammar -> 'c grammar
  = fun l1 cond l2 ->
    apply_position idt (conditional_fsequence l1 cond l2)

let fixpoint :  'a -> ('a -> 'a) grammar -> 'a grammar
  = fun a f1 ->
    let res = declare_grammar "fixpoint" in
    let _ = set_grammar res
      (mk_grammar [(Empty(Simple a),Container.create ());
       next res Idt (next f1 Idt idtEmpty)]) in
    res

let fixpoint1 :  'a -> ('a -> 'a) grammar -> 'a grammar
  = fun a f1 ->
    let res = declare_grammar "fixpoint" in
    let _ = set_grammar res
      (mk_grammar [next f1 (Simple(fun f -> f a)) idtEmpty;
       next res Idt (next f1 Idt idtEmpty)]) in
    res

let delim g = g

let rec alternatives : 'a grammar list -> 'a grammar = fun g ->
  mk_grammar (List.flatten (List.map snd g))

(* FIXME: optimisation: modify g inside when possible *)
let position g =
  apply_position (fun a buf pos buf' pos' ->
    (filename buf, line_num buf, pos, line_num buf', pos', a)) g

let handle_exception f a =
  try f a with Parse_error(buf, pos, msgs) ->
    begin
      Printf.eprintf "File %S, line %d, character %d:\n"
        (filename buf) (line_num buf) (utf8_col_num buf pos);
      Printf.eprintf "Parse error:\n%!";
      List.iter (Printf.eprintf " - %s\n%!") msgs;
      failwith "No parse."
    end

let grammar_family ?(param_to_string=(fun _ -> "<...>")) name =
  let tbl = EqHashtbl.create ~equal:closure_eq 31 in
  let is_set = ref None in
  (fun p ->
    try EqHashtbl.find tbl p
    with Not_found ->
      let g = declare_grammar (name^"_"^param_to_string p) in
      EqHashtbl.add tbl p g;
      (match !is_set with None -> ()
      | Some f ->
         set_grammar g (f p);
      );
      g),
  (fun f ->
    (*if !is_set <> None then invalid_arg ("grammar family "^name^" already set");*)
    is_set := Some f;
    EqHashtbl.iter (fun p r ->
      set_grammar r (f p);
    ) tbl)

let blank_grammar grammar blank buf pos =
    let save_debug = !debug_lvl in
    debug_lvl := !debug_lvl / 10;
    let (_,buf,pos) = internal_parse_buffer (init_errpos buf pos) grammar blank buf pos in
    debug_lvl := save_debug;
    if !debug_lvl > 0 then Printf.eprintf "exit blank %d %d\n%!" (line_num buf) pos;
    (buf,pos)

let accept_empty grammar =
  try
    ignore (parse_string grammar no_blank ""); true
  with
    Parse_error _ -> false

let change_layout : ?old_blank_before:bool -> ?new_blank_after:bool -> 'a grammar -> blank -> 'a grammar
  = fun ?(old_blank_before=true) ?(new_blank_after=true) l1 blank1 ->
    let i = Fixpoint.from_val (false, Charset.full) in
    (* compose with a test with a full charset to pass the final charset test in
       internal_parse_buffer *)
    let l1 = mk_grammar [next l1 Idt (next (test Charset.full (fun _ _ -> (), true))
                               (Simple (fun _ a -> a)) idtEmpty)] in
    let fn errpos _ buf pos buf' pos' =
      let buf,pos = if old_blank_before then buf', pos' else buf, pos in
      let (a,buf,pos) = internal_parse_buffer errpos l1 blank1
        ~blank_after:new_blank_after buf pos in
      (a,buf,pos)
    in
    greedy_solo i fn

let greedy : 'a grammar -> 'a grammar
  = fun l1 ->
    (* compose with a test with a full charset to pass the final charset test in
       internal_parse_buffer *)
    let l1 = mk_grammar [next l1 Idt (next (test Charset.full (fun _ _ -> (), true))
                                                   (Simple (fun _ a -> a)) idtEmpty)] in
    (* FIXME: blank are parsed twice. internal_parse_buffer should have one more argument *)
    let fn errpos blank buf pos _ _ =
      let (a,buf,pos) = internal_parse_buffer errpos l1 blank buf pos in
      (a,buf,pos)
    in
    greedy_solo (fst l1) fn

let grammar_info : type a. a grammar -> info = fun g -> (force (fst g))

let dependent_sequence : 'a grammar -> ('a -> 'b grammar) -> 'b grammar
  = fun l1 f2 ->
    let tbl = EqHashtbl.create ~equal:closure_eq 31 in
          mk_grammar [next l1 Idt (Dep (fun a ->
              try EqHashtbl.find tbl a
              with Not_found ->
                let res = grammar_to_rule (f2 a) in
                EqHashtbl.add tbl a res; res
          ), Container.create ())]

let iter : 'a grammar grammar -> 'a grammar
  = fun g -> dependent_sequence g (fun x -> x)
