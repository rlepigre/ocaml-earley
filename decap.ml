open Charset
open Input
open Str

let debug_lvl = ref 0
let _ = Printexc.record_backtrace true

exception Give_up of string
exception Error

let give_up s = raise (Give_up s)

type blank = buffer -> int -> buffer * int

let no_blank str pos = str, pos

let blank_regexp r =
  let r = Str.regexp r in
  let accept_newline = string_match r "\n" 0 && match_end () = 1 in
  let rec fn str pos =
    let str,pos = normalize str pos in
    if string_match r (line str) pos then
      let pos' = match_end () in
      if accept_newline && pos' = String.length (line str) && not (is_empty str pos') then fn str pos'
      else str, pos'
    else str, pos
  in
  fn


type info = bool * Charset.t
type _ pos =
  | Idt : ('a -> 'a) pos
  | Simple : 'a -> 'a pos
  | WithPos : (buffer -> int -> buffer -> int -> 'a) -> 'a pos

type assoc_cell = Obj.t ref

(** A BNF grammar is a list of rules. The type parameter ['a] corresponds to
    the type of the semantics of the grammar. For example, parsing using a
    grammar of type [int grammar] will produce a value of type [int]. *)
type 'a grammar = info Fixpoint.t * 'a rule list

and 'a symbol =
  | Term of Charset.t * (buffer -> int -> 'a * buffer * int)
  (** terminal symbol just read the input buffer *)
  | Test of Charset.t * (buffer -> int -> 'a * bool)
  (** test *)
  | NonTerm of info Fixpoint.t * 'a rule list
  (** non terminal *)
  | RefTerm of info Fixpoint.t * 'a rule list ref
  (** non terminal trough a reference to define recursive rule lists *)

(** BNF rule. *)
and _ rule =
  | Empty : 'a pos * assoc_cell -> 'a rule
  (** Empty rule. *)
  (*  | Dep : (('a -> 'c rule) -> 'c rule) rule -> 'a rule*)
  (** Dependant rule *)
  | Next : info Fixpoint.t * string * bool * 'a symbol * ('a -> 'b) pos * ('b -> 'c) rule * assoc_cell -> 'c rule
  (** Sequence of a symbol and a rule. then bool is to ignore blank after symbol. *)

(* type de la table de Earley *)
type position = buffer * int
type ('a,'b,'c,'r) cell = {
  ignb:bool; (*ignb!ignore next blank*)
  debut : position;
  debut_after_blank : position;
  fin   : position;
  stack : ('c, 'r) element list ref;
  acts  : 'a list;
  rest  : 'b rule;
  full  : 'c rule }

and (_,_) element =
  | C : (('a -> 'b -> 'c) pos, 'b, 'c, 'r) cell -> ('a,'r) element
  | B : ('a -> 'b) pos list -> ('a,'b) element

and _ final   = D : (('b -> 'c), 'b, 'c, 'r) cell -> 'r final

(* si t : table et t.(j) = (i, R, R' R) cela veut dire qu'entre i et j on a parsé
   la règle R' et qu'il reste R à parser. On a donc toujours
   i <= j et R suffix de R' R (c'est pour ça que j'ai écris R' R)
*)

type ('a,'b) eq  = Eq : ('a, 'a) eq | Neq : ('a, 'b) eq

let (===) : type a b.a -> b -> (a,b) eq = fun r1 r2 ->
  if Obj.repr r1 == Obj.repr r2 then Obj.magic Eq else Neq

let eq_closure : type a b. a -> b -> bool =
  fun f g ->
    let open Obj in
    let adone = ref [] in
    let rec fneq f g =
      f == g ||
	match is_int f, is_int g with
	| true, true -> f = g
	| false, true | true, false -> false
	| false, false ->
	   if !debug_lvl > 10 then Printf.eprintf "*%!";
	   let ft = tag f and gt = tag g in
	   if ft = forward_tag then (
	     if !debug_lvl > 10 then Printf.eprintf "#%!";
	     fneq (field f 0) g)
	   else if gt = forward_tag then (
	     if !debug_lvl > 10 then Printf.eprintf "#%!";
	     fneq f (field g 0))
	   else if ft = custom_tag || gt = custom_tag then f = g
	   else if ft <> gt then false
	   else (if !debug_lvl > 10 then Printf.eprintf " %d %!" ft;
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

let eq_pos (buf,pos) (buf',pos') = eq_buf buf buf' && pos = pos'

let eq_D (D {debut; rest; full; ignb; stack})
         (D {debut=d'; rest=r'; full=fu'; ignb=ignb'; stack = stack'}) =
  eq_pos debut d' && eq rest r' && eq full fu' && ignb=ignb' && (assert (eq stack stack'); true)

let eq_C c1 c2 = eq c1 c2 ||
  match c1, c2 with
    (C {debut; rest; full; ignb; stack; acts},
     C {debut=d'; rest=r'; full=fu'; ignb=ignb'; stack = stack'; acts = acts'}) ->
      eq_pos debut d' && eq rest r' && eq full fu' && ignb=ignb' && (assert (eq stack stack'); eq_closure acts acts')
  | (B acts, B acts') -> eq_closure acts acts'
  | _ -> false

let new_cell, is_unset, unset =
  let x = Obj.repr (0,0) in
  (fun () -> ref x), (fun c -> !c == x), (fun c -> c := x)


let idt = fun x -> x
let idtCell = new_cell ()
let idtEmpty : type a.(a->a) rule = Empty(Idt,idtCell)

let apply_pos: type a b.a pos -> buffer -> int -> buffer -> int -> a =
  fun f b p b' p' ->
    match f with
    | Idt -> idt
    | Simple f -> f
    | WithPos f -> f b p b' p'

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

let new_name =
  let c = ref 0 in
  (fun () ->
    let x = !c in
    c := x + 1;
    "G__" ^ string_of_int x)

let grammar_to_rule : type a.a grammar -> a rule = fun (i,g) ->
  match g with
  | [r] -> r
  | _ -> Next(i,new_name (),false,NonTerm(i,g),Idt,idtEmpty,new_cell ())

let iter_rules : type a.(a rule -> unit) -> a rule list -> unit = List.iter

let force = Fixpoint.force

let empty = Fixpoint.from_val (true, Charset.empty_charset)
let any = Fixpoint.from_val (true, full_charset)

let rule_info:type a.a rule -> info Fixpoint.t = function
  | Next(i,_,_,_,_,_,_) -> i
  | Empty _ -> empty
(*  | Dep(_) -> any*)

let symbol_info:type a.a symbol -> info Fixpoint.t  = function
  | Term(i,_) -> Fixpoint.from_val (false,i)
  | NonTerm(i,_) -> i
  | RefTerm(i,_) -> i
  | Test(set,_) -> Fixpoint.from_val (true, set)

let compose_info i1 i2 =
  let i1 = symbol_info i1 in
  match i2 with
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
  Fixpoint.from_funl g (false, Charset.empty_charset) or_info

let rec print_rule : type a.out_channel -> a rule -> unit = fun ch rule ->
    match rule with
    | Next(_,name,_,_,_,rs,_) -> Printf.fprintf ch "%s %a" name print_rule rs
    (*    | Dep _ -> Printf.fprintf ch "DEP "*)
    | Empty _ -> ()

let print_final ch (D {rest; full}) =
  let rec fn : type a.a rule -> unit = fun rule ->
    if eq rule rest then Printf.fprintf ch "* " ;
    match rule with
    | Next(_,name,_,_,_,rs,_) -> Printf.fprintf ch "%s " name; fn rs
    (*    | Dep _ -> Printf.fprintf ch "DEP "*)
    | Empty _ -> ()
  in
  fn full;
  let (ae,set) = force (rule_info rest) in
  Printf.fprintf ch "(%a %b)" print_charset set ae

let print_element ch el =
  let rec fn : type a b.a rule -> b rule -> unit = fun rest rule ->
    if eq rule rest then Printf.fprintf ch "* " ;
    match rule with
    | Next(_,name,_,_,_,rs,_) -> Printf.fprintf ch "%s " name; fn rest rs
    (*    | Dep _ -> Printf.fprintf ch "DEP "*)
    | Empty _ -> ()
  in
  match el with
  | C {rest; full} ->
     fn rest full;
     let (ae,set) = force (rule_info rest) in
     Printf.fprintf ch "(%a %b)" print_charset set ae
  | B _ ->
    Printf.fprintf ch "B"

type _ dep_pair = P : 'a rule * ('a, 'b) element list ref * (('a, 'b) element -> unit) ref -> 'b dep_pair

type 'a dep_pair_tbl = assoc_cell list ref

let find r dlr =
  match r with
  | Next(_,_,_,_,_,_,c) | Empty(_,c) ->
     if is_unset c then raise Not_found else Obj.magic !c

let add r p dlr =
  match r with
  | Next(_,_,_,_,_,_,c) | Empty(_,c) ->
     if is_unset c then
       (dlr := c::!dlr; c := Obj.repr p)
    else
       assert false

let memo_assq : type a b. a rule -> b dep_pair_tbl -> ((a, b) element -> unit) -> unit =
  fun r dlr f ->
    try match find r dlr with
      P(r',ptr,g) ->
	match r === r' with
	| Eq -> g := (let g = !g in (fun el -> f el; g el)); List.iter f !ptr;
	| _ -> assert false
    with Not_found ->
      add r (P(r,ref [], ref f)) dlr

let add_assq : type a b. a rule -> (a, b) element  -> b dep_pair_tbl -> (a, b) element list ref =
  fun r el dlr ->
    try match find r dlr with
      P(r',ptr,g) ->
	match r === r' with
	| Eq ->
	   if not (List.exists (eq_C el) !ptr) then (
	     if !debug_lvl > 3 then
	       Printf.eprintf "add stack %a ==> %a\n%!" print_rule r print_element el;
	     ptr := el :: !ptr; !g el); ptr
	| _ -> assert false
    with Not_found ->
      if !debug_lvl > 3 then
	Printf.eprintf "add stack %a ==> %a\n%!" print_rule r print_element el;
      let res = ref [el] in add r (P(r,res, ref (fun el -> ()))) dlr; res

let find_assq : type a b. a rule -> b dep_pair_tbl -> (a, b) element list ref =
  fun r dlr ->
    try match find r dlr with
      P(r',ptr,g) ->
	match r === r' with
	| Eq -> ptr
	| _ -> assert false
    with Not_found ->
      let res = ref [] in add r (P(r,res, ref (fun el -> ()))) dlr; res

let solo = fun ?(name=new_name ()) set s ->
  let i = (false,set) in
  let j = Fixpoint.from_val i in
  (j, [Next(j,name,false,Term (set, s),Idt,idtEmpty,new_cell ())])

let test = fun ?(name=new_name ()) set f ->
  let i = (true,set) in
  let j = Fixpoint.from_val i in
  (j, [Next(j,name,false,Test (set, f),Idt,idtEmpty, new_cell ())])

let nonterm (i,s) = NonTerm(i,s)

let next_aux name b s f r = Next(compose_info s r, name, b, s,f,r, new_cell ())

let next : type a b c. ?ignb:bool -> a grammar -> (a -> b) pos -> (b -> c) rule -> c rule =
  fun ?(ignb=false) s f r -> match snd s with
  | [Next(i,name,ignb0,s0,g,Empty(h,_),_)] ->
     next_aux name (ignb||ignb0) s0 (compose3 f h g) r
  | _ -> next_aux (new_name ()) ignb (nonterm s) f r


let debut = function D { debut } -> debut
let fin   = function D { fin   } -> fin
let is_term = function D { rest= Next(_,_,_,Term _,_,_,_) } -> true | _ -> false

type 'a pos_tbl = (int * int, 'a final list) Hashtbl.t

let find_pos_tbl t (buf,pos) = Hashtbl.find t (buf_ident buf, pos)
let add_pos_tbl t (buf,pos) v = Hashtbl.replace t (buf_ident buf, pos) v
let char_pos (buf,pos) = line_beginning buf + pos


let merge_acts o n =
  let rec fnacts acc = function
    | [] -> acc
    | a::l -> if List.exists (eq_closure a) acc then fnacts acc l else fnacts (a::acc) l
  in fnacts o n

(* ajoute un élément dans la table et retourne true si il est nouveau *)
let add : string -> 'a final -> 'a pos_tbl -> bool =
  fun info element old ->
    let debut = debut element in
    let oldl = try find_pos_tbl old debut with Not_found -> [] in
    let rec fn acc = function
      | [] ->
	 if !debug_lvl > 1 then Printf.eprintf "add %s %a %d %d\n%!" info print_final element
	   (char_pos debut) (char_pos (fin element));
	add_pos_tbl old debut (element :: oldl); true
      | e::es ->
	 (match e, element with
	   D {debut; debut_after_blank; fin; rest; full; ignb; stack; acts},
           D {debut=d'; fin=f'; rest=r'; full=fu'; ignb=ignb'; stack = stack'; acts = acts'}
	 ->
	 (match
           eq_pos debut d', rest === r', full === fu', ignb=ignb', acts, acts' with
           | true, Eq, Eq, true, act, acts' ->
	      assert(stack == stack' || (Printf.eprintf "add %s assert failure %a %a \n%!" info print_final element print_final e; false));
	   let acts0 = merge_acts acts acts' in
	   if not (acts0 == acts) then (
	     if true || !debug_lvl > 1 then
	       Printf.eprintf "merging %s %a %d %d\n%!" info print_final element
		 (char_pos d') (char_pos fin);
	     add_pos_tbl old debut
	       (List.rev_append acc (D {debut; debut_after_blank; fin; rest; full; ignb; stack; acts=acts0}::es))
	     );
	   false
	 | _ ->
	    fn (e::acc) es))
    in fn [] oldl

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
	| B _       -> ()
      end) els
  in
  match el with D {stack} -> fn (cast_elements !stack); !res

let expected s = raise Error
let unexpected s = raise Error

let protect f a =
  try
    f a
  with Give_up _ | Error -> ()

let protect_cons f a acc =
  try
    f a :: acc
  with Give_up _ | Error -> acc

let combine_list : type a b. (a -> b) -> a list -> b list =
  fun f l1 ->
  let rec fn acc l = match acc, l with
    | [], [] -> assert false
    | acc, [] -> List.rev acc
    | [], [a] -> [f a]
    | acc, a::l ->
       let acc = protect_cons f a acc in
       fn acc l
  in fn [] l1

let combine f l = combine_list (pos_apply f) l

let combine_list2 f l1 l2 = List.flatten (combine_list (fun x -> combine_list (f x) l2) l1)

let combine2 : type a0 a1 a2 b c.(a2 -> b) list -> (b -> c) pos list -> (a1 -> a2) pos -> (a0 -> a1) pos -> (a0 -> c) pos list =
  fun acts acts' g f -> combine_list2 (fun f1 f2 -> compose f2 (pos_apply (fun g x -> f1 (g x)) (compose g f))) acts acts'

let combine1 : type a b c d.(c -> d) list -> (a -> b) pos -> (a -> (b -> c) -> d) pos list =
   fun acts g -> combine_list (fun f1 -> pos_apply (fun g x h -> f1 (h (g x))) g) acts


(* phase de lecture d'un caractère, qui ne dépend pas de la bnf *)
let lecture : type a.int -> buffer -> int -> buffer -> int -> a pos_tbl -> a final buf_table -> a final buf_table =
  fun id buf0 pos0 buf pos elements tbl ->
    if !debug_lvl > 3 then Printf.eprintf "read at line = %d col = %d (%d)\n%!" (line_beginning buf0) pos0 id;
    if !debug_lvl > 2 then Printf.eprintf "read after blank line = %d col = %d (%d)\n%!" (line_beginning buf) pos id;
    let tbl = ref tbl in
    Hashtbl.iter (fun _ l -> List.iter (function
    | D {debut; debut_after_blank; fin; stack;acts; rest; full;ignb} as element ->
       match rest with
       | Next(_,_,ignb0,Term (_,f),g,rest0,_) ->
	  (try
	     let dab = if eq rest full && not ignb then (buf,pos) else debut_after_blank in
	     let buf0, pos0 = if ignb then buf0, pos0 else buf, pos in
	     (* Printf.eprintf "lecture at %d %d\n%!" (line_beginning buf0) pos0;*)
	     let a, buf, pos = f buf0 pos0 in
	     if !debug_lvl > 1 then
	       Printf.eprintf "action for terminal of %a =>" print_final element;
             let a = try apply_pos g buf0 pos0 buf pos a
	       with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
	     if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
	     let state =
	       (D {debut; debut_after_blank = dab;fin=(buf, pos); stack;
		   acts = combine_list (fun acts f -> acts (f a)) acts; rest=rest0; full;ignb=ignb0})
	     in
	     tbl := insert_buf buf pos state !tbl
	   with Error | Give_up _ -> ())

       | _ -> ()) l) elements;
    !tbl

(* selectionnne les éléments commençant par un terminal
   ayant la règle donnée *)
type 'b action = { a : 'a.'a rule -> ('a, 'b) element list ref -> unit }

let pop_final : type a. a dep_pair_tbl -> a final -> a action -> unit =
  fun dlr element act ->
    match element with
    | D {rest=rule; acts; full; debut; debut_after_blank; fin; stack;ignb} ->
       match rule with
       | Next(_,_,_,(NonTerm(_,rules) | RefTerm(_,{contents = rules})),f,rest,_) ->
	  let is_eq = eq rule full in
	 (match rest, true || is_eq with
	 | Empty (g,_), false ->
	    if !debug_lvl > 1 then Printf.eprintf "RIGHT RECURSION OPTIM %a\n%!" print_final element;
	    iter_rules (fun r ->
	      let complete = protect (function
		| C {rest; acts=acts'; full; debut; stack;ignb=i} ->
		   let c = C {rest; acts=combine2 acts acts' g f; full;
			      debut; debut_after_blank; fin; stack;ignb=ignb||i} in
 		     ignore(add_assq r c dlr)
		| B acts' ->
		     let c = B (combine2 acts acts' g f) in
		     ignore (add_assq r c dlr))
	      in
	      assert (!stack <> []);
	      if eq_pos debut fin then memo_assq full dlr complete
	      else List.iter complete !stack;
	      act.a r (find_assq r dlr)) rules
	 | rest, _ ->
	     let c = C {rest; acts=combine1 acts f; full; debut; debut_after_blank;
			fin; stack;ignb} in
	     iter_rules (fun r -> act.a r (add_assq r c dlr)) rules);

       | _ -> assert false

let taille_tables els forward =
  let adone = ref [] in
  let res = ref 0 in
  Hashtbl.iter (fun _ els -> List.iter (fun el -> res := !res + taille el adone) els) els;
  iter_buf forward (fun el -> res := !res + taille el adone);
  !res

let good c i =
  let (ae,set) = force i in
  if !debug_lvl > 3 then Printf.eprintf "good %c %b %a" c ae Charset.print_charset set;
  let res = ae || Charset.mem set c in
  if !debug_lvl > 3 then Printf.eprintf " => %b\n%!" res;
  res


(* fait toutes les prédictions et productions pour un element donné et
   comme une prédiction ou une production peut en entraîner d'autres,
   c'est une fonction récursive *)
let rec one_prediction_production
 : type a. a final -> a pos_tbl -> a dep_pair_tbl -> buffer -> int -> buffer -> int -> char -> char ->  unit
 = fun element elements dlr buf pos buf' pos' c c' ->
   match element with
  (* prediction (pos, i, ... o NonTerm name::rest_rule) dans la table *)
   | D {debut=i; debut_after_blank=i0; fin=j; acts; stack; rest; full;ignb=ignb0} as element0 ->
     if !debug_lvl > 1 then Printf.eprintf "predict/product for %a\n%!" print_final element0;
     match rest with
     | Next(info,_,_,(NonTerm (_) | RefTerm(_)),_,_,_) when good (if ignb0 then c' else c) info ->
	let acts =
	  { a = (fun rule stack ->
	    if good (if ignb0 then c' else c) (rule_info rule) then (
	      let nouveau = D {debut=j; debut_after_blank = j; fin=j; acts = [idt]; stack; rest = rule; full = rule; ignb=ignb0} in
	      let b = add "P" nouveau elements in
	      if b then one_prediction_production nouveau elements dlr buf pos buf' pos' c c'))
	  }
	in
	pop_final dlr element acts

     (* production	(pos, i, ... o ) dans la table *)
     | Empty(a,_) ->
	(try
	   if !debug_lvl > 1 then
	     Printf.eprintf "action for completion of %a =>" print_final element;
           let x = try combine_list (fun f -> f (apply_pos a (fst i0) (snd i0) (fst j) (snd j))) acts
	           with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
	   if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
	  let complete element =
	    match element with
	    | C {debut=k; debut_after_blank=k'; fin=i'; stack=els'; acts; rest; full;ignb} ->
	       let ignb = ignb||ignb0 in
	       if good (if ignb then c' else c) (rule_info rest) then begin
		 if !debug_lvl > 1 then
		   Printf.eprintf "action for completion bis of %a =>" print_final element0;
		 let x = try combine_list2 (fun f x -> apply_pos f (fst k') (snd k') (fst j) (snd j) x)acts x
	           with e -> if !debug_lvl > 1 then Printf.eprintf "fails\n%!"; raise e in
		 if !debug_lvl > 1 then Printf.eprintf "succes\n%!";
		 let nouveau = D {debut=k; debut_after_blank=if eq_pos k i' then i0 else k';
				  acts = x; fin=j; stack=els'; rest; full;ignb} in
		 let b = add "C" nouveau elements in
		 if b then one_prediction_production nouveau elements dlr buf pos buf' pos' c c'
	       end
	    | B _ -> ()
	  in
	  let complete = protect complete in
	  if eq_pos i j then memo_assq full dlr complete
	  else List.iter complete !stack;
	 with Give_up _ | Error -> ())
(*     | Dep rest ->
	let rest = rest acts in
	if good c (rule_info rest) then begin
	  let nouveau = D {debut=i; debut_after_blank=i0; fin=j; acts; stack; rest; full;ignb=ignb0} in
	  let b = add "D" nouveau elements in
	  if b then one_prediction_production buf pos c c' rec_err dlr elements nouveau
       end*)
     | Next(_,_,ignb,Test(s,f),g,rest,_) ->
	(try
	  let (a,b) = if ignb0 then f buf' pos' else f buf pos in
	  if b then begin
	    let nouveau = D {debut=i; debut_after_blank=i0; fin=j;
			     acts = combine_list (fun f h -> f (h (apply_pos g (fst i0) (snd i0) (fst j) (snd j) a))) acts;
			     stack; rest; full;ignb} in
	    let b = add "D" nouveau elements in
	    if b then one_prediction_production nouveau elements dlr  buf pos buf' pos' c c'
	  end
	 with Give_up _ | Error -> ())
     | _ -> ()

(* fait toutes les prédictions productions pour les entrées de la
   table à la position indiquée *)
let prediction_production : type a.buffer -> int -> buffer -> int -> char -> char -> a pos_tbl -> unit
  = fun buf pos buf' pos' c c' elements ->
    let dlr = ref [] in
    Hashtbl.iter ((fun _ l ->
      List.iter (fun el -> one_prediction_production el elements dlr buf pos buf' pos' c c') l))
      elements;
    List.iter unset !dlr

exception Parse_error of string * int * int * string list * string list

let c = ref 0
let parse_buffer_aux : type a.bool -> a grammar -> blank -> buffer -> int -> a * buffer * int =
  fun internal main blank buf0 pos0 ->
    Fixpoint.debug := !debug_lvl > 2;
    let parse_id = incr c; !c in
    (* construction de la table initiale *)
    let elements : a pos_tbl = Hashtbl.create 31 in
    let r0 : a rule = grammar_to_rule main in
    let s0 : (a, a) element list ref = ref [B [Idt]] in
    let bp = (buf0,pos0) in
    let _ = add "I" (D {debut=bp; fin=bp; debut_after_blank = bp;
			acts = [idt]; stack=s0; rest=r0; full=r0;ignb=false}) elements in
    let pos = ref pos0 and buf = ref buf0 in
    let forward = ref empty_buf in
    let parse_error () =
      if internal then raise Error else
	raise (Parse_error (fname !buf, line_num !buf, !pos, [], []))
    in
    (* boucle principale *)
    let continue = ref true in
    let count_empty = ref 0 in
    while !continue && !count_empty < 10 do
      let buf', pos' = blank !buf !pos in
      let c,_,_ = Input.read buf' pos' in
      let c',_,_ = Input.read !buf !pos in
      if !debug_lvl > 0 then Printf.eprintf "parse_id = %d, line = %d, pos = %d, taille =%d, %C, %C\n%!"
	 parse_id (line_num !buf) !pos (taille_tables elements !forward) c c';
      prediction_production buf' pos' !buf !pos c c' elements;
      forward := lecture parse_id !buf !pos buf' pos' elements !forward;
      let l =
	try
	  let (buf', pos', l, forward') = pop_firsts_buf !forward in
	  pos := pos';
	  buf := buf';
	  forward := forward';
	  l
	with Not_found -> []
      in
      if is_empty !buf !pos then incr count_empty;
      if l = [] then continue := false else
	begin
	  Hashtbl.clear elements;
	  List.iter (fun s -> ignore (add "L" s elements)) l;
	end
    done;
    (* on regarde si on a parsé complètement la catégorie initiale *)
    let rec fn : type a.a list -> a final list -> a list = fun acc -> function
      | [] -> acc
      | D {debut=(b,i); stack=s1; rest=Empty(f,_); acts; full=r1} :: els ->
	 assert(eq_buf b buf0 &&  i = pos0);
	 let x = combine_list (fun a -> a (apply_pos f buf0 pos0 !buf !pos)) acts in
	 let rec gn acc = function
	   | B (ls)::l ->
	      let ls = combine_list2 (fun f x -> apply_pos f buf0 pos0 !buf !pos x) ls x in
	      gn (List.rev_append ls acc) l
	   | C _:: l -> gn acc l
	   | [] -> fn acc els
	 in
	 gn acc !s1
      | _ :: els -> fn acc els
    in
    let la = fn [] (try find_pos_tbl elements (buf0,pos0) with Not_found -> []) in
    let a = match la with
      | a::_::_ -> Printf.eprintf "%d parse trees" (1 + List.length la); a
      | a::_ -> a
      | _ -> parse_error ()
    in
    (a, !buf, !pos)

let partial_parse_buffer : type a.a grammar -> blank -> buffer -> int -> a * buffer * int
   = fun g bl buf pos ->
       parse_buffer_aux false g bl buf pos

let internal_parse_buffer : type a.a grammar -> blank -> buffer -> int -> a * buffer * int
  = fun g bl buf pos -> parse_buffer_aux true g bl buf pos

let eof : 'a -> 'a grammar
  = fun a ->
    let fn buf pos =
      if is_empty buf pos then (a,buf,pos) else expected "EOF"
    in
    solo (Charset.singleton '\255') fn

let mk_grammar s = (grammar_info s, s)

let apply : type a b. (a -> b) -> a grammar -> b grammar = fun f l1 ->
  mk_grammar [next l1 (Simple f) idtEmpty]

let apply_position : type a b. (a -> buffer -> int -> buffer -> int -> b) -> a grammar -> b grammar = fun f l1 ->
  mk_grammar [next l1 Idt (Empty(WithPos(fun b p b' p' a -> f a b p b' p'),new_cell ()))]

let sequence : 'a grammar -> 'b grammar -> ('a -> 'b -> 'c) -> 'c grammar
  = fun l1 l2 f -> mk_grammar [next l1 Idt (next l2 (Simple (fun b a -> f a b)) idtEmpty)]

let sequence_position : 'a grammar -> 'b grammar -> ('a -> 'b -> buffer -> int -> buffer -> int -> 'c) -> 'c grammar
   = fun l1 l2 f ->
    mk_grammar [next l1 Idt (next l2 Idt (Empty(WithPos(fun b p b' p' a' a -> f a a' b p b' p'),new_cell ())))]

(*
let rec rule_apply : type a b. (a -> b) -> a rule -> b rule = fun f -> function
  | Empty(a,_) -> Empty(f a,new_cell ())
  | EmptyPos(a,_) -> EmptyPos((fun b p b' p' -> f (a b p b' p')),new_cell ())
  | Next(i,s,b,t,g,r,_) -> Next(i,s,b,t,g,rule_apply (fun g a -> f (g a)) r, new_cell ())

let apply : type a b. (a -> b) -> a grammar -> b grammar = fun f (i,g) ->
  (i, List.map (rule_apply f) g)

let apply_position : type a b. (a -> buffer -> int -> buffer -> int -> b) -> a grammar -> b grammar = fun f (i,g) ->
  let rec fn : type a b. (a -> buffer -> int -> buffer -> int -> b) -> a rule -> b rule = fun f -> function
    | Empty(a,_) -> EmptyPos((fun b p b' p' -> f a b p b' p'),new_cell ())
    | EmptyPos(a,_) -> EmptyPos((fun b p b' p' -> f (a b p b' p') b p b' p'),new_cell ())
    | Next(i,s,b,t,g,r,_) -> Next(i,s,b,t,g,fn (fun g b p b' p' a -> f (g a) b p b' p') r, new_cell ())
  in
  (i, List.map (fn f) g)

let sequence : 'a grammar -> 'b grammar -> ('a -> 'b -> 'c) -> 'c grammar
  = fun l1 l2 f -> mk_grammar [next l1 idt (rule_apply (fun b a -> f a b) (grammar_to_rule l2))]

let sequence_position : 'a grammar -> 'b grammar -> ('a -> 'b -> buffer -> int -> buffer -> int -> 'c) -> 'c grammar
   = fun l1 l2 f ->
    apply_position idt (sequence l1 l2 f)
*)
let parse_buffer : 'a grammar -> blank -> buffer -> 'a =
  fun g blank buf ->
    let g = sequence g (eof ()) (fun x _ -> x) in
    let (a, _, _) = partial_parse_buffer g blank buf 0 in
    a

let parse_string ?(filename="") grammar blank str =
  let str = buffer_from_string ~filename str in
  parse_buffer grammar blank str

let partial_parse_string ?(filename="") grammar blank str =
  let str = buffer_from_string ~filename str in
  partial_parse_buffer grammar blank str

let parse_channel ?(filename="") grammar blank ic  =
  let str = buffer_from_channel ~filename ic in
  parse_buffer grammar blank str

let parse_file grammar blank filename  =
  let str = buffer_from_file filename in
  parse_buffer grammar blank str

let fail : string -> 'a grammar
  = fun msg ->
    let fn buf pos =
      unexpected msg
    in
    solo Charset.empty_charset fn (* make sure we have the message *)

let unset : string -> 'a grammar
  = fun msg ->
    let fn buf pos =
      failwith msg
    in
    solo Charset.empty_charset fn (* make sure we have the message *)

let declare_grammar name =
  let g = snd (unset (name ^ " not set")) in
  let ptr = ref g in
  let j = Fixpoint.from_ref ptr grammar_info in
  mk_grammar [Next(j,name,false,RefTerm (j, ptr),Idt, idtEmpty,new_cell ())]

let set_grammar : type a.a grammar -> a grammar -> unit = fun p1 p2 ->
  match snd p1 with
  | [Next(_,name,_,RefTerm(i,ptr),f,e,_)] ->
     (match f === Idt, e === idtEmpty  with
     | Eq, Eq -> ptr := snd p2; Fixpoint.update i;
     | _ -> invalid_arg "set_grammar")
  (*Printf.eprintf "setting %s %b %a\n%!" name ae Charset.print_charset set;*)
  | _ -> invalid_arg "set_grammar"

let include_grammar : type a.a grammar -> a grammar = fun p1 ->
  match snd p1 with
  | [Next(_,name,_,RefTerm(i,ptr),f,e,_)] ->
     (match f === Idt, e === idtEmpty  with
     | Eq, Eq -> (i,!ptr)
     | _ -> invalid_arg "include_grammar")
  | [Next(_,name,_,NonTerm(i,l),f,e,_)] ->
     (match f === Idt, e === idtEmpty  with
     | Eq, Eq -> (i,l)
     | _ -> invalid_arg "include_grammar")
  (*Printf.eprintf "setting %s %b %a\n%!" name ae Charset.print_charset set;*)
  | _ -> invalid_arg "set_grammar"

let grammar_name : type a.a grammar -> string = fun p1 ->
  match snd p1 with
  | [Next(_,name,_,_,_,Empty _,_)] -> name
  | _ -> new_name ()

let char : ?name:string -> char -> 'a -> 'a grammar
  = fun ?name c a ->
    let msg = Printf.sprintf "%C" c in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c', buf', pos' = read buf pos in
      if c = c' then (a,buf',pos') else expected msg
    in
    solo ~name (Charset.singleton c) fn

let in_charset : ?name:string -> charset -> char grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "%s" (String.concat "|" (list_of_charset cs)) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c, buf', pos' = read buf pos in
      if mem cs c then (c,buf',pos') else expected msg
    in
    solo ~name cs fn

let not_in_charset : ?name:string -> charset -> unit grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "^%s" (String.concat "|" (list_of_charset cs)) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c, buf', pos' = read buf pos in
      if mem cs c then ((), false) else ((), true)
    in
    test ~name (Charset.complement cs) fn

let relax : unit grammar =
  test Charset.full_charset (fun _ _ -> (),true)

let any : char grammar
  = let fn buf pos =
      let c', buf', pos' = read buf pos in
      (c',buf',pos')
    in
    solo ~name:"ANY" Charset.full_charset fn

let debug msg : unit grammar
    = let fn buf pos =
	Printf.eprintf "%s file:%s line:%d col:%d\n%!" msg (fname buf) (line_num buf) pos;
	((), true)
      in
      test ~name:msg Charset.empty_charset fn

let string : ?name:string -> string -> 'a -> 'a grammar
  = fun ?name s a ->
    if s = "" then invalid_arg "Decap.string";
    let name = match name with None -> s | Some n -> n in
    let fn buf pos =
      let buf = ref buf in
      let pos = ref pos in
      let len_s = String.length s in
      for i = 0 to len_s - 1 do
        let c, buf', pos' = read !buf !pos in
        if c <> s.[i] then expected s;
        buf := buf'; pos := pos'
      done;
      (a,!buf,!pos)
    in
    solo ~name (Charset.singleton s.[0]) fn

let regexp : ?name:string -> string ->  ((int -> string) -> 'a) -> 'a grammar
  = fun ?name r0  a ->
    let r = Str.regexp r0 in
    let name = match name with None -> String.escaped r0 | Some n -> n in
    let set = Charset.copy empty_charset in
    let found = ref false in
    for i = 0 to 254 do
      let s = String.make 1 (Char.chr i) in
      if Str.string_partial_match r s 0 && Str.match_end () > 0 then
        (found := true; addq set (Char.chr i))
    done;
    if not !found then failwith "regexp: illegal empty regexp";
    (*let ae = Str.string_match r "" 0 in*)
    (*    if ae then invalid_arg "Decap.regexp"; FIXME*)
    let fn buf pos =
      let l = line buf in
      if pos > String.length l then expected name;
      if string_match r l pos then (
        let f n = matched_group n l in
        let pos' = match_end () in
	let res = try a f with Give_up msg -> unexpected msg in
	(res,buf,pos'))
      else expected name
    in
    solo ~name set fn

(* charset is now useless ... will be suppressed soon *)
let black_box : (buffer -> int -> 'a * buffer * int) -> charset -> bool -> string -> 'a grammar
  = fun fn set ae name -> solo ~name set fn

let empty : 'a -> 'a grammar = fun a -> (empty,[Empty (Simple a, new_cell ())])

let sequence3 : 'a grammar -> 'b grammar -> 'c grammar -> ('a -> 'b -> 'c -> 'd) -> 'd grammar
  = fun l1 l2 l3 f ->
    sequence l1 (sequence l2 l3 (fun x y z -> f z x y)) (fun z f -> f z)

let fsequence : 'a grammar -> ('a -> 'b) grammar -> 'b grammar
  = fun l1 l2 -> mk_grammar [next l1 Idt (grammar_to_rule l2)]

let fsequence_position : 'a grammar -> ('a -> buffer -> int -> buffer -> int -> 'b) grammar -> 'b grammar
  = fun l1 l2 ->
    apply_position idt (fsequence l1 l2)

(*
let dependent_sequence : 'a grammar -> ('a -> 'b grammar) -> 'b grammar
  = fun l1 f2 ->
    let tbl = Ahash.create 31 in
    mk_grammar [next l1 (Dep (fun a ->
      try Ahash.find tbl a
      with Not_found ->
	let res = grammar_to_rule (f2 a) in
	Ahash.replace tbl a res;
	res
    ))]


let iter : 'a grammar grammar -> 'a grammar
  = fun g -> dependent_sequence g (fun x -> x)
*)

let conditional_sequence : 'a grammar -> ('a -> bool) -> 'b grammar -> ('a -> 'b -> 'c) -> 'c grammar
  = fun l1 cond l2 f ->
    mk_grammar (List.map (next l1 (Simple(fun x -> if cond x then x else give_up "condition fail")))
		  (snd (apply (fun b a -> f a b) l2)))

let conditional_fsequence : 'a grammar -> ('a -> bool) -> ('a -> 'b) grammar -> 'b grammar
  = fun l1 cond l2 ->
    mk_grammar (List.map (next l1 (Simple(fun x -> if cond x then x else give_up "condition fail")))
		  (snd l2))

let option : 'a -> 'a grammar -> 'a grammar
  = fun a (_,l) -> mk_grammar (Empty (Simple a,new_cell())::l)

let fixpoint :  'a -> ('a -> 'a) grammar -> 'a grammar
  = fun a f1 ->
    let res = declare_grammar "fixpoint" in
    let _ = set_grammar res
      (mk_grammar [Empty(Simple a,new_cell ());
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
(*
  let rec fn (next_tbl, empty_tbl, empty_pos_tbl) = function
    | Next(i,name,ign,s,f,r,_) ->
       (gn [] (i,ign,s,f) name r next_tbl,  empty_tbl, empty_pos_tbl)
    | Empty(f,_) ->
       if List.exists (eq_closure f) empty_tbl then
	 (next_tbl,  empty_tbl, empty_pos_tbl)
       else
	 (next_tbl,  (f::empty_tbl), empty_pos_tbl)
    | EmptyPos(f,_) ->
       if List.exists (eq_closure f) empty_pos_tbl then
	 (next_tbl,  empty_tbl, empty_pos_tbl)
       else
	 (next_tbl,  empty_tbl, (f::empty_pos_tbl))

  and gn : type a b c. a assoc list -> (info Fixpoint.t * bool * b symbol * (b -> c)) -> string -> (c -> a) rule -> a assoc list -> a assoc list = fun acc key name r -> function
    | [] -> List.rev_append acc [A(key,name,[r])]
    | A(key',name',l) as c::ls ->
       match key ==== key' with
	 Eq -> Printf.eprintf "merge\n%!"; List.rev_append acc (A(key',name',(r::l))::ls)
       | _ -> gn (c::acc) key name r ls

  in

  let rec main : type a. a rule list -> a grammar = fun l ->
    let (next_tbl,empty_tbl,empty_pos_tbl) = List.fold_left fn ([], [], []) l in
    let g = [] in
    let g = List.fold_left (fun g f -> Empty(f,new_cell ())::g) g empty_tbl in
    let g = List.fold_left (fun g f -> EmptyPos(f,new_cell ())::g) g empty_pos_tbl in
    let g = List.fold_left (fun g (A((i,ign,s,f), name, l)) ->
      match l with
      | [] -> assert false
      | [r] -> Next(i,name,ign,s,f,r,new_cell ())::g
      | _ -> Next(i,name,ign,s,f,grammar_to_rule (main l), new_cell ())::g) g next_tbl
    in
    mk_grammar g
  in
    main (List.flatten (List.map snd g))*)
  mk_grammar (List.flatten (List.map snd g))

(* FIXME: optimisation: modify g inside when possible *)
let position g =
  apply_position (fun a buf pos buf' pos' ->
    (fname buf, line_num buf, pos, line_num buf', pos', a)) g

let print_exception = function
  | Parse_error(fname,l,n,msg, expected) ->
     let expected =
       if expected = [] then "" else
	 Printf.sprintf "'%s' expected" (String.concat "|" expected)
     in
     let msg = if msg = [] then "" else (String.concat "," msg)
     in
     let sep = if msg <> "" && expected <> "" then ", " else "" in
     Printf.eprintf "File %S, line %d, characters %d-%d:\nParse error:%s%s%s\n%!" fname l n n msg sep expected
  | _ -> assert false

let handle_exception f a =
  try f a with Parse_error _ as e -> print_exception e; failwith "No parse."

(* cahcing is useless in decap2 *)
let cache g = g

let active_debug = ref true

let grammar_family ?(param_to_string=fun _ -> "X") name =
  let tbl = Ahash.create 31 in
  let is_set = ref None in
  (fun p ->
    try Ahash.find tbl p
    with Not_found ->
      let g = declare_grammar (name^"_"^param_to_string p) in
      Ahash.replace tbl p g;
      (match !is_set with None -> ()
      | Some f ->
	 set_grammar g (f p);
      );
      g),
  (fun f ->
    if !is_set <> None then invalid_arg ("grammar family "^name^" already set");
    is_set := Some f;
    Ahash.iter (fun p r ->
      set_grammar r (f p);
    ) tbl)

let blank_grammar grammar blank buf pos =
  let save_debug = !debug_lvl in
  debug_lvl := !debug_lvl / 10;
  let (_,buf,pos) = partial_parse_buffer grammar blank buf pos in
  debug_lvl := save_debug;
  (buf,pos)

let accept_empty grammar =
  try
    ignore (parse_string grammar no_blank ""); true
  with
    Parse_error _ -> false

let change_layout : 'a grammar -> blank -> 'a grammar
  = fun l1 blank1 ->
    (* compose with a test with a full_charset to pass the final charset test in
       internal_parse_buffer *)
    let l1 = sequence l1 (test full_charset (fun _ _ -> (), true)) (fun x _ -> x) in
    let fn buf pos =
      let (a,buf,pos) = internal_parse_buffer l1 blank1 buf pos in
      (a,buf,pos)
    in
    let (ae, set) = force (fst l1) in
    solo (*FIXME:ae = true*) set fn

let ignore_next_blank : 'a grammar -> 'a grammar = fun g ->
  mk_grammar [next ~ignb:true g Idt idtEmpty]

let merge _ = failwith "merge unimplemented"
let lists _ = failwith "lists unimplemented"

let grammar_info : type a. a grammar -> info = fun g -> (force (fst g))
