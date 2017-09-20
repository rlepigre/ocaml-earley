(* Equality types *)
type ('a,'b) eq  = Eq : ('a, 'a) eq | Neq : ('a, 'b) eq

type _ tag = ..

type clist =
  | Cons : 'a tag * 'a * clist -> clist
  | Nil  : clist

 and t = { mutable contents : clist
         ; adr : int }

 and 'a table = { id : 'a tag
                ; eq : 'b. 'b tag -> ('a,'b) eq
                ; mutable hi : t Weak.t list }

let create =
  let c = ref 0 in
  (fun () ->
    let adr = !c in
    c := adr + 1;
    { contents = Nil; adr })

let address t = t.adr

let rec memw x l = match l with
  | [] -> false
  | w::l -> match Weak.get w 0 with
            | Some y when x == y -> true
            | _ -> memw x l

let add : type a. a table -> t -> a -> unit = fun t c a ->
  if memw c t.hi then (
    let rec fn = function
      | Nil -> assert false
      | Cons(tag,x,r) ->
         match t.eq tag with
         | Eq -> Cons(tag,a,r)
         | Neq -> Cons(tag,x,fn r)
    in
    c.contents <- fn c.contents
  ) else (
    c.contents <- Cons(t.id,a,c.contents);
    let w = Weak.create 1 in
    Weak.set w 0 (Some c);
    t.hi <- w :: t.hi)

let rec find_aux : type a. a table -> clist -> a = fun t c ->
  match c with
  | Nil -> raise Not_found
  | Cons(tag,x,r) ->
     match t.eq tag with
     | Eq  -> x
     | Neq -> find_aux t r

let find : type a. a table -> t -> a = fun t c -> find_aux t c.contents

let reset : type a. a table -> unit = fun t ->
  let rec fn = function
    | Nil -> invalid_arg "reset"
    | Cons(tag,x,r) ->
       match t.eq tag with
       | Eq -> r
       | Neq -> Cons(tag,x,fn r)
  in
  List.iter (fun w ->
      match Weak.get w 0 with
       | Some l -> l.contents <- fn l.contents
       | None -> ()) t.hi;
  t.hi <- []

let create_table : type a.unit -> a table = fun () ->
  let module M = struct type _ tag += T : a tag end in
  let eq : type b.b tag -> (a, b) eq =
    function M.T -> Eq | _ -> Neq
  in
  let res = {id = M.T; eq; hi=[]} in
  Gc.finalise reset res;
  res
