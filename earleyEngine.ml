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

(* Exception raised for parse error. Can be raise in the action of a
   grammar using [give_up] *)
exception Error

(* identity is often used *)
let idt x = x


(* A blank function is just a function progressing in a buffer *)
type blank = buffer -> int -> buffer * int

(** Positions *)
type position = buffer * int

(* Type for action with or without position and its combinators *)
type _ pos =
  | Idt : ('a -> 'a) pos
  | Simple : 'a -> 'a pos
  | WithPos : (buffer -> int -> buffer -> int -> 'a) -> 'a pos

let apply_pos: type a.a pos -> buffer -> int -> buffer -> int -> a =
  fun f buf col buf' col' ->
    match f with
    | Idt -> idt
    | Simple f -> f
    | WithPos f -> f buf col buf' col'

(** Common combinators, easy from their types *)
let app_pos:type a b.(a -> b) pos -> a pos -> b pos = fun f g ->
  match f,g with
  | Idt, _ -> g
  | Simple f, Idt -> Simple(f idt)
  | WithPos f, Idt -> WithPos(fun b p b' p' -> f b p b' p' idt)
  | Simple f, Simple g -> Simple(f g)
  | Simple f, WithPos g -> WithPos(fun b p b' p' -> f (g b p b' p'))
  | WithPos f, Simple g -> WithPos(fun b p b' p' -> f b p b' p' g)
  | WithPos f, WithPos g -> WithPos(fun b p b' p' -> f b p b' p' (g b p b' p'))

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
    | WithPos g, WithPos h  ->
       WithPos(fun b p b' p' -> f (g b p b' p') (h b p b' p'))

let pos_apply3
    : type a b c d.(a -> b -> c -> d) -> a pos -> b pos -> c pos -> d pos =
  fun f a b c -> app_pos (pos_apply2 f a b) c

(** for terminals: get the start position and returns a value with
    the final position *)
type 'a input = buffer -> int -> 'a * buffer * int

(** type for Greedy: get both the position before and after blank *)
type 'a input2 = buffer -> int -> 'a input

(** type for tests: get also both position and return a boolean and
    a value *)
type 'a test  = buffer -> int -> buffer -> int -> 'a * bool

(** Position record stored in the elements of the earley table.
    We store the position before and after the blank *)
type pos2 = { buf : buffer; col : int; buf_ab  : buffer; col_ab : int }

(** Some function on pos2 *)
let eq_pos {buf;col} {buf=buf';col=col'} =
  buffer_equal buf buf' && col = col'

let apply_pos_start =
  fun f ({ buf_ab; col_ab } as p1) ({buf;col} as p2) ->
    (** parse nothing : pos_ab *)
    if eq_pos p1 p2 then apply_pos f buf_ab col_ab buf_ab col_ab
    (** parse something *)
    else apply_pos f buf_ab col_ab buf col

(* For prediction, we need to fix the position of the beginning for an action *)
let fix_begin : type a.a pos -> pos2 -> a pos =
  fun f p ->
    match f with
    | WithPos f -> let f = f p.buf_ab p.col_ab in
                   WithPos (fun _ _ p1 p2 -> f p1 p2)
    | x -> x

(** Type of the information computed on a rule: the boolean tells if
    the grammar can parse an empty string and the charset, the first accepted
    characteres when the rule is used to parse something. *)
type info = bool * Charset.t

(** THE MAIN TYPES *)

(** A BNF grammar is a list of rules. The type parameter ['a] corresponds to
    the type of the semantics of the grammar. For example, parsing using a
    grammar of type [int grammar] will produce a value of type [int]. *)

module rec Types : sig
  (** The type of a grammar, with its information *)
  type 'a grammar = info Fixpoint.t * 'a rule list
   (** The symbol, a more general concept that terminals *)
   and _ symbol =
     | Term : Charset.t * 'a input -> 'a symbol
     (** terminal symbol just read the input buffer *)
     | Greedy : info Fixpoint.t * (blank -> 'a input2) -> 'a symbol
     (** Greedy correspond to a recursive call to the parser. We
         can change the blank function for instance, or parse
         input as much as possible. In fact it is only in the
         combinators in earley.ml that we use Greedy to call
         the parser back. *)
     | Test : Charset.t * 'a test -> 'a symbol
     (** Test on the input, can for instance read blanks, usefull for
         things like ocamldoc (but not yet used by earley-ocaml). *)
     | NonTerm : info Fixpoint.t * 'a rule list ref -> 'a symbol
     (** Non terminals trough a reference to define recursive rule lists *)

   (** BNF rule. *)
   and _ prerule =
     | Empty : 'a pos -> 'a prerule
     (** Empty rule. *)
     | Dep : ('a -> 'b rule) -> ('a -> 'b) prerule
     (** Dependant rule, gives a lot of power! but costly! use only when
         no other solution are possible *)
     | Next : info Fixpoint.t * string * 'a symbol * ('a -> 'b) pos *
                ('b -> 'c) rule -> 'c prerule
     (** Sequence of a symbol and a rule, with a possible name for debugging,
         the information on the rule, the symbol to read, an action and
         the rest of the rule *)

   (** Each rule holds a container to associate data to the rule in O(1).
       see below the description of the type ('a,'b) pre_stack *)
   and 'a rule = { rule : 'a prerule
                 ; ptr : 'a StackContainer.container
                 ; adr : int }

   (** Type of an active element of the earley table.
       In a description of earley, an element is
       [(start, end, done * rest)] meaning we parsed
       the string from [pos1] to [pos2] with the rule [done]
       and it remains to parse [rest]. The '*' therefore denote
       the current position. Earley is basically a dynamic algorithm
       producing all possible elements.

       We depart from this representation in two ways:

       - we do not represent [done], we keep the whole whole rule:
         [full = done rest]

       - we never keep [end]. It is only used when we finish parsing of
         a rule and we have an element [(start, end, done * Empty)]
         then, we look for other element of the form
         [(start', end', done' * rest')] where
              * end' = start
              * rest' starts with a non terminal containing done
         We represent this situation by a stack in the element
         [(start, end, done * Empty)], that is maintained to lists
         all the elements satisfying the above property (no more,
         no less, each element only once)

         The type ['a final] represent an element of the earley table
         where [end] is the current position in the string being parsed.
    *)
   and _ final = D :
    { start : pos2           (* position in the buffer, before and after blank *)
    ; stack : ('c, 'r) stack (* tree of stack of what should be do after
                                reading the [rest] of the rule *)
    ; acts  : 'b -> 'c       (* action to produce the final 'c. *)
    ; rest  : 'b rule        (* remaining to parse, will produce 'b *)
    ; full  : 'c rule        (* full rule. rest is a suffix of full. *)
    } -> 'r final


   (** Type of the element that appears in stack. Note: all other
       elements will be collected by the GC, which is what we want to
       release memory.

       The type is similar to the previous: [('a, 'r) element], means
       that from a value of type 'a, comming from our parent in the stack,
       we could produce a value of type ['r] using [rest].

       The action needs to be prametrised by the future position which
       is unknown.
    *)
   and (_,_) element =
     (* Cons cell of the stack *)
     | C : { start : pos2
           ; stack : ('c, 'r) stack
           ; acts  : ('a -> 'b -> 'c) pos
           ; rest  : 'b rule
           ; full  : 'c rule
           } -> ('a,'r) element
     (* End of the stack *)
     | B : ('a -> 'r) pos -> ('a,'r) element

   (** stack themselves are in acyclic graph of elements (sharing is
       important to be preserved). We need a reference for the stack
       construction.
    *)
   and ('a,'b) stack = ('a,'b) element list ref

  (** For the construction of the stack, all elements of the
      same list ref of type ('a,'b) have the same [end'].
      And all elements that points to this stack have the
      [start = end']. Moreover, all elements with the
      same [full] and [start] must point to the same stack.
      Recall that [end] is not represented in elements.

      We call the position [end'] associated to a stack (as
      sait the [start] of the element point to this stack, the
      "stack position". An important point: stack are only
      constructed when the stack position is the current position.

      And if we omit the "right recursion optimisation", when
      we add a point from an element (start, end, rest, full)
      to a stack (which is therefore at position [start], we
      have [start = end] and [rest = full]. The rule has not
      parsed anything! The is the "prediction" phase of earley.

      To do this construction, we use the record below with
      a hook that we run on all elements added to that stack.
      This record is only used we stack whose position are the
      current position: all these records will become inaccessible
      when we advance in parsing.

      Morevoer, a direct pointer (thanks to the Container module)
      is kept from the [full] rule of all elements point to
      these stack and that have the current position as [end].
      This is the role of the functor call below.
 *)


  (** stack in construction ... they have a hook, to run on
      elements added to the stack later ! *)
   type ('a,'b) pre_stack =
     { stack : ('a, 'b) stack
     ; mutable hooks : (('a, 'b) element -> unit) list }

end = Types

   (** Use container to store a point to the rule in stack, we
       use recursive module for that *)
and StackContainer : Container.Param
                   with type ('b,'a) elt = ('a,'b) Types.pre_stack =
  Container.Make(struct type ('b,'a) elt = ('a,'b) Types.pre_stack end)

include Types

(** Recal the INVARIANTS:

1° Consider two C elements (or two D elements) of a stack.  If their
   have the same start, rest and full is means we have parsed the same
   prefix of the rule from start to produce a value of the same type.

   Then, the two elements MUST HAVE PHYSICALLY EQUAL stack

2° For D nodes only, we keep only one for each (start, rest, full) triple
   so acts are necessarily physically equal
*)

(** a function to build rule from pre_rule *)
let count_rule = ref 0 (** counet outside because of value restriction *)
let mkrule : type a. a prerule -> a rule = fun rule ->
  let adr = let c = !count_rule in count_rule := c+1; c in
  { rule; ptr = StackContainer.create (); adr  }

(** rule equlity: we use a little of magic. In 4.04.0 and above,
    we could avoid it using extensible GADT, the it costs two fields
    in each rule. It is safe in the case as the type of rule is
    abstract. *)
let eq_rule : type a b. a rule -> b rule -> (a, b) eq =
  fun r1 r2 -> if Obj.repr r1 == Obj.repr r2
               then Obj.magic Eq
               else Neq

(** Equality for stack element: as we keep the invariant, we only
    need physical equality. You may uncomment the code below
    to check this. *)
let eq_C : type a b.(a,b) element -> (a,b) element -> bool =
  fun c1 c2 -> c1 == c2
  (*
    let res =
      match c1, c2 with
        (C {start; rest; full; stack; acts},
         C {start=s'; rest=r'; full=fu'; stack = stack'; acts = acts'}) ->
        begin
          match eq_pos start s', eq_rule rest r', eq_rule full fu' with
          | true, Eq, Eq -> assert (stack == stack'); eq_closure acts acts'
          | _ -> false
        end
      | (B acts, B acts') -> eq_closure acts acts'
      | _ -> false
        in
        if res then assert (c1 == c2);
        res *)

(** Equality on a final needs to do a comparison as it is used to test
    if a new element is already present.*)
let eq_D (D {start; rest; full; stack; acts})
         (D {start=start'; rest=rest'; full=full'; stack=stack'; acts=acts'}) =
  eq_pos start start' &&
    match eq_rule rest rest', eq_rule full full' with
    | Eq, Eq -> assert(acts == acts'); assert(stack == stack'); true
    | _ -> false

(** Some rules/grammar contruction that we need already here *)
let idtEmpty : type a.unit -> (a->a) rule = fun () -> mkrule (Empty Idt)

let new_name =
  let c = ref 0 in
  (fun () ->
    let x = !c in
    c := x + 1;
    "G__" ^ string_of_int x)

let grammar_to_rule : type a.?name:string -> a grammar -> a rule
  = fun ?name (info,rules) ->
    match rules with
    | [r] when name = None -> r
    | _ ->
       let name = match name with None -> new_name () | Some n -> n in
       mkrule (Next(info,name,NonTerm(info,ref rules),Idt,idtEmpty ()))

(** Basic constants/functions for rule information *)
let force = Fixpoint.force
let empty = Fixpoint.from_val (true, Charset.empty)
let any   = Fixpoint.from_val (true, Charset.full)

(** managment of info = accept empty + charset accepted as first char *)
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

(* Printing *)
let rec print_rule : type a b.?rest:b rule -> out_channel -> a rule -> unit =
  fun ?rest ch rule ->
    begin
      match rest with
      | None -> ()
      | Some rest ->
         match eq_rule rule rest with Eq -> Printf.fprintf ch "* " | Neq -> ()
    end;
    match rule.rule with
    | Next(_,name,_,_,rs) -> Printf.fprintf ch "%s %a" name (print_rule ?rest) rs
    | Dep _ -> Printf.fprintf ch "DEP"
    | Empty _ -> ()

let print_pos1 ch (buf, col) =
  Printf.fprintf ch "%d:%d" (line_num buf) col

let print_pos2 ch {buf; col; buf_ab; col_ab} =
  Printf.fprintf ch "%d:%d-%d:%d" (line_num buf) col (line_num buf_ab) col_ab

let print_final ch (D {start; rest; full}) =
  Printf.fprintf ch "%a " print_pos2 start;
  print_rule ~rest ch full;
  let (ae,set) = force (rule_info rest) in
  if !debug_lvl > 0 then Printf.fprintf ch "(%a %b)" Charset.print set ae

let print_element : type a b.out_channel -> (a,b) element -> unit = fun ch el ->
  match el with
  | C {start; rest; full} ->
     Printf.fprintf ch "%a " print_pos2 start;
     print_rule ~rest ch full;
     let (ae,set) = force (rule_info rest) in
     if !debug_lvl > 0 then Printf.fprintf ch "(%a %b)" Charset.print set ae
  | B _ ->
    Printf.fprintf ch "B"

let print_rule ch rule = print_rule ?rest:None ch rule

(** Here are the 3 type for tables used by out algorithm *)

(** This type is the state of the parsing table for the current position
    it only hold ['a final] elements whose [end] are the current position *)
type 'a cur = (int * int * int * int, 'a final) Hashtbl.t

(** type of a table with pending reading, that is elements resulting from
    reading the string with some symbols. We need this table, because two
    terminal symbols could read different length of the input from the
    same point *)
type 'a reads = 'a final OrdTbl.t ref

(** heart of our code: stack construction. The type below, denotes table
    associate stack to rule. Recall we construct stack for element whose
    end are the current position *)
type 'a sct = 'a StackContainer.table

(** [add_stack_hook sct rule fn] adds in [table] a hook [fn] for the given
    [rule]. [fn] will be called each time an element is added to the stack
    of pointed by that [rule]. The hook is run on the existing elements
    if the stack. The stack is created if it did not exists yet *)
let add_stack_hook : type a b. b sct -> a rule -> ((a, b) element -> unit) -> unit =
  fun sct r f ->
    try
      let {stack; hooks } as p = StackContainer.find sct r.ptr in
      p.hooks <- f::hooks; List.iter f !stack
    with Not_found ->
      StackContainer.add sct r.ptr {stack = ref []; hooks = [f]}

(** [add_stack sct rule element] add the given [element] to the stack of
    the given [rule] in the table [sct]. Runs all hook if any. Creates
    the table if needed *)
let add_stack : type a b. b sct -> a rule -> (a, b) element -> (a, b) stack =
  fun sct r el ->
    try
      let { stack; hooks } = StackContainer.find sct r.ptr in
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
      StackContainer.add sct r.ptr {stack; hooks=[]};
      stack

(** [find_stack sct rule] finds the stack to associate to the given rule *)
let find_stack : type a b. b sct -> a rule -> (a, b) stack =
  fun sct r ->
    try
      let { stack } = StackContainer.find sct r.ptr in stack
    with Not_found ->
      let stack = ref [] in
      StackContainer.add sct r.ptr {stack; hooks=[]};
      stack

(** Get the key of an element *)
let elt_key : type a. a final -> int * int * int * int =
  function D { start = {buf;col}; rest; full } ->
    (buffer_uid buf, col, full.adr, rest.adr)

(** Test is a given char is accepted by the given rule *)
let good c rule =
  let i = rule_info rule in
  let (ae,set) = force i in
  let res = ae || Charset.mem set c in
  if !debug_lvl > 4 then Printf.eprintf "good %C %b %a => %b\n"
                                        c ae Charset.print set res;
  res

(** Adds an element in the current table of elements, return true if it is
    new *)
let add : string -> pos2 -> char -> 'a final -> 'a cur -> bool =
  fun msg pos_final c element elements ->
    let test = match element with D { rest } -> good c rest in
    let key = elt_key element in
    test &&
      begin
        try
          let e = Hashtbl.find elements key in
          (match e, element with
             D {start=s; rest; full; stack; acts},
             D {start=s'; rest=r'; full=fu'; stack = stack'; acts = acts'} ->
             match eq_rule rest r', eq_rule full fu' with
             | Eq, Eq ->
                if not (eq_closure acts acts') && !warn_merge then
                  Printf.eprintf "\027[31mmerging %a %a %a\027[0m\n%!"
                    print_final element print_pos2 s print_pos2 pos_final;
(*                assert(stack == stack' ||
                 (Printf.eprintf
                    "\027[31mshould be the same stack %s %a %a %a\027[0m\n%!"
                    info print_final element print_pos2 s print_pos1 pos_final;
                  false));*)
                false
             | _ -> assert false)
        with Not_found ->
         if !debug_lvl > 1 then
             Printf.eprintf "add %s %a\n%!" msg print_final element;
          Hashtbl.add elements key element; true
      end

(** Computes the size of an element stack, taking in account sharing *)
let taille : 'a final -> (Obj.t, Obj.t) stack -> int = fun el adone ->
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

(** Computes the size of the two tables, forward reading and the current
    elements *)
let taille_tables els forward =
  if !debug_lvl > 0 then
    let adone = ref [] in
    let res = ref 0 in
    Hashtbl.iter (fun _ el -> res := !res + 1 + taille el adone) els;
    OrdTbl.iter forward (fun el -> res := !res + 1 + taille el adone);
    !res
  else 0

(** Combinators for actions, these are just the combinators we need, contructed
    from there type *)

(** This one for completion *)
let cns : type a b c.a -> (b -> c) -> ((a -> b) -> c) = fun a f g -> f (g a)

(** This one for prediction with right recursion optimisation *)
let combine2 : type a0 a1 a2 b bb c.(a2 -> b) -> (b -> c) pos -> (a1 -> a2) pos
                    -> (a0 -> a1) pos -> (a0 -> c) pos =
  fun acts acts' g f ->
    pos_apply3 (fun acts' g f x -> acts' (acts (g (f x)))) acts' g f

(** This one for normal prediction *)
let combine1 : type a b c d.(c -> d) -> (a -> b) pos
                    -> (a -> (b -> c) -> d) pos =
  fun acts g -> pos_apply (fun g a -> let b = g a in fun f -> acts (f b)) g

(** Protection from give_up: just do nothing *)
let protect f a = try f a with Error -> ()

(* This is now the main function computing all the consequences of the
   element given at first argument.
   It needs
   - the three tables
   - the blank (to pass it to Greedy grammars)
   - the position and current charaters for the action and the good test

   It perform prediction/production/lecture in a recursive way.
 *)
let rec pred_prod_lec
        : type a. a final -> a cur -> a reads -> a sct -> blank
               -> pos2 -> char -> unit =
  fun element0 elements forward sct blank cur_pos c ->
  let rec fn element0 =
    match element0 with
    | D {start; acts; stack; rest; full} ->
       match rest.rule with
       (** A non terminal : production *)
       | Next(info,_,(NonTerm(_,{contents = rules})),f,rest2) ->
          (* select the useful rules *)
          let rules = List.filter (fun rule -> good c rule) rules in
          (** we need to fix the start for the action f and g for
              right recursive optim *)
          let f = fix_begin f cur_pos in
          (** Compute the elements to add in the stack of all created rules *)
          let tails =
            match rest2.rule, eq_pos start cur_pos with
            | Empty (g), false ->
               (* NOTE: right recursion optim is bad for rule with only one
                  non terminal.
                  - loops for grammar like A = A | ...
                  NOTE: more merge may appends without right recursion *)
               let g = fix_begin g start in
               (** We contract the head of the stack. This is similar
                   to tail call optimisation in compilation *)
               let contract = function
                 | C {rest; acts=acts'; full; start; stack} ->
                    C {rest; acts=combine2 acts acts' g f; full; start; stack}
                 | B acts' ->
                    B (combine2 acts acts' g f)
               in
               List.map contract !stack
            | _ ->
               [C {rest=rest2; acts=combine1 acts f; full; start; stack}]
          in
          (** create one final elements for each rule and adds the
              tails to its stack *)
          let start = cur_pos in
          List.iter
            (fun rule ->
              let stack = find_stack sct rule in
                let nouveau = D {start; acts = idt; stack; rest = rule; full = rule}
                in
                let b = add "P" cur_pos c nouveau elements in
                List.iter (fun c -> ignore (add_stack sct rule c)) tails;
                if b then fn nouveau;
            ) rules

    (* production      (pos, i, ... o ) dans la table *)
     | Empty(a) ->
        (try
           if !debug_lvl > 1 then
             Printf.eprintf "action for completion of %a =>" print_final element0;
           let x = try acts (apply_pos_start a start cur_pos)
                   with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
           if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
          let complete = fun element ->
            match element with
            | C {start; stack=els'; acts; rest; full} ->
               if !debug_lvl > 1 then
                 Printf.eprintf "action for completion test %a" print_element element;
               if good c rest then begin
                 if !debug_lvl > 1 then
                   Printf.eprintf "action for completion bis of %a =>" print_final element0;
                 let acts =
                   try apply_pos_start acts start cur_pos x
                   with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e
                 in
                 if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
                 let nouveau = D {start; acts; stack=els'; rest; full } in
                 let b = add "C" cur_pos c nouveau elements in
                 if b then fn nouveau
               end
            | B _ -> ()
          in
          let complete = protect complete in
          if eq_pos start cur_pos then add_stack_hook sct full complete
          else List.iter complete !stack;
         with Error -> ())

         | Dep(rule) ->
       if !debug_lvl > 1 then Printf.eprintf "dependant rule\n%!";
       let a =
         let a = ref None in
         try let _ = acts (fun x -> a := Some x; raise Exit) in assert false
         with Exit ->
           match !a with None -> assert false | Some a -> a
       in
       let cc = C { start;
                    acts = Simple (fun b f -> f (acts (fun _ -> b))); stack;
                   rest = idtEmpty (); full } in
       let rule = rule a in
       let stack' = add_stack sct rule cc in
       let start = cur_pos in
       let nouveau = D {start; acts = idt; stack = stack'; rest = rule; full = rule } in
       let b = add "P" cur_pos c nouveau elements in
       if b then fn nouveau


       | Next(_,_,Test(s,f),g,rest) ->
          (try
             let {buf; col; buf_ab; col_ab} as j = cur_pos in
             (*if !debug_lvl > 1 then Printf.eprintf "testing at %d %d\n%!"
                                                   (line_num buf0) col0;*)
             let (a,b) = f buf col buf_ab col_ab in
             if b then begin
                 if !debug_lvl > 1 then Printf.eprintf "test passed\n%!";
                 let x = apply_pos g buf col buf col a in
                 let nouveau = D {start; stack; rest; full; acts = cns x acts} in
                 let b = add "T" cur_pos c nouveau elements in
                 if b then fn nouveau
               end
           with Error -> ())

       | Next(_,_,Term (_,f),g,rest) ->
          (try
             (*Printf.eprintf "lecture at %d %d\n%!" (line_num buf0) pos0;*)
             let {buf_ab; col_ab} = cur_pos in
             let a, buf, col = f buf_ab col_ab in
             if !debug_lvl > 1 then
               Printf.eprintf "action for terminal of %a =>" print_final element0;
             let a = try apply_pos g buf_ab col_ab buf col a
               with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
             if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
             let nouveau =
               (D {start; stack; acts = cns a acts; rest; full})
             in
             if buffer_before buf col buf_ab col_ab then
               begin
                 let b = add "L" cur_pos c nouveau elements in
                 if b then fn nouveau
               end
             else
               forward := OrdTbl.add buf col nouveau !forward
           with Error -> ())

       | Next(_,_,Greedy(_,f),g,rest) ->
          (try
             let {buf; col; buf_ab; col_ab} = cur_pos in
             if !debug_lvl > 0 then Printf.eprintf "greedy at %d %d\n%!" (line_num buf_ab) col_ab;
             let a, buf, col = f blank buf col buf_ab col_ab in
             if !debug_lvl > 1 then
               Printf.eprintf "action for greedy of %a =>" print_final element0;
             let a = try apply_pos g buf_ab col_ab buf col a
               with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
             if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
             let nouveau =
               (D {start; stack; acts = cns a acts; rest; full})
             in
             if buffer_before buf col buf_ab col_ab then
               begin
                   let b = add "G" cur_pos c nouveau elements in
                   if b then fn nouveau
               end
             else
               forward := OrdTbl.add buf col nouveau !forward
           with Error -> ())
  in fn element0

exception Parse_error of Input.buffer * int * string list

let count = ref 0

let rec tail_key : type a. a rule -> int = fun rule ->
  match rule.rule with
  | Next(_,_,_,_,rest) -> tail_key rest
  | Empty _ -> rule.adr
  | Dep _ -> assert false (* FIXME *)

let parse_buffer_aux : type a.bool -> bool -> a grammar -> blank -> buffer -> int -> a * buffer * int =
  fun internal blank_after main blank buf0 col0 ->
    let parse_id = incr count; !count in
    (* construction de la table initiale *)
    let elements : a cur = Hashtbl.create 61 in
    let r0 : a rule = grammar_to_rule main in
    let final_elt = B (Simple idt) in
    let final_key = (buffer_uid buf0, col0, r0.adr, tail_key r0) in
    let s0 : (a, a) stack = ref [final_elt] in
    let col = ref col0 and buf = ref buf0 in
    let buf', col' = blank buf0 col0 in
    let start = { buf = buf0; col = col0; buf_ab = buf'; col_ab = col' } in
    let col' = ref col' and buf' = ref buf' in
    let init = D {start; acts = idt; stack=s0; rest=r0; full=r0 } in
    let last_success = ref [] in
    let forward = ref OrdTbl.empty in
    let todo = ref [init] in
    if !debug_lvl > 0 then Printf.eprintf "entering parsing %d at line = %d(%d), col = %d(%d)\n%!"
      parse_id (line_num !buf) (line_num !buf') !col !col';
    let sct = StackContainer.create_table 101 in
    let one_step l =
      let c,_,_ = Input.read !buf' !col' in
      let c',_,_ = Input.read !buf !col in
      let cur_pos = { buf = !buf; col = !col; buf_ab = !buf'; col_ab = !col' } in
      if !debug_lvl > 0 then Printf.eprintf "parsing %d: line = %d(%d), col = %d(%d), char = %C-%C\n%!" parse_id (line_num !buf) (line_num !buf') !col !col' c c';
      List.iter (fun s ->
        if add "I" cur_pos c s elements then
          pred_prod_lec s elements forward sct blank cur_pos c) l;
    in
    let search_success () =
      try
        let success = Hashtbl.find elements final_key in
        last_success := (!buf,!col,!buf',!col',success) :: !last_success
      with Not_found -> ()
    in

    (* boucle principale *)
    while !todo <> [] do
      StackContainer.clear sct;
      Hashtbl.clear elements;
      one_step !todo;
      if internal then search_success ();
      if !debug_lvl > 0 then
        Printf.eprintf
          "parse_id = %d, line = %d(%d), col = %d(%d), taille =%d\n%!"
          parse_id (line_num !buf) (line_num !buf') !col !col'
          (taille_tables elements !forward);
      try
         let (new_buf, new_col, l, forward') = OrdTbl.pop !forward in
         todo := l;
         forward := forward';
         col := new_col; buf := new_buf;
         let buf'', col'' = blank new_buf new_col in
         buf' := buf''; col' := col'';
       with Not_found -> todo := []
    done;
    if not internal then search_success ();
    (* on regarde si on a parsé complètement la catégorie initiale *)
    let parse_error () =
      if internal then
        raise Error
      else
        raise (Parse_error (!buf', !col', []))
    in
    if !debug_lvl > 0 then Printf.eprintf "searching final state of %d at line = %d(%d), col = %d(%d)\n%!" parse_id (line_num !buf) (line_num !buf') !col !col';
    let rec fn : type a.a final -> a = function
      | D {stack=s1; rest={rule=Empty f}; acts; full=r1} ->
         (match eq_rule r0 r1 with Neq -> raise Error | Eq ->
           let x = acts (apply_pos f buf0 col0 !buf !col) in
           let gn : type a b. b -> (b,a) element list -> a =
            fun x l ->
              let rec hn =
                function
                | B (ls)::l ->
                   (try apply_pos ls buf0 col0 !buf !col x
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
    let a, buf, col as result =
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
    StackContainer.clear sct; (* don't forget final cleaning of assoc ptrs !! *)
    (* useless but clean *)
    if !debug_lvl > 0 then
      Printf.eprintf "exit parsing %d at line = %d, col = %d\n%!" parse_id (line_num buf) col;
    result

let internal_parse_buffer : type a.a grammar -> blank -> ?blank_after:bool -> buffer -> int -> a * buffer * int
   = fun g bl ?(blank_after=false) buf col ->
       parse_buffer_aux true blank_after g bl buf col
