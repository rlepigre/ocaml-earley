(* Equality types *)
type ('a,'b) eq  = Eq : ('a, 'a) eq | Neq : ('a, 'b) eq

type _ tag = ..

type clist =
  | Cons : 'a tag * 'a * clist -> clist
  | Nil  : clist

type cell = { mutable contents : clist
           ; adr : int }

module T = struct
  type t = cell
  let hash t = t.adr
  let equal t1 t2 = t1 == t2
end

type t = cell

module Hash = Weak.Make(T)

type 'a table = { id : 'a tag
               ; eq : 'b. 'b tag -> ('a,'b) eq
               ; hi : Hash.t }


let create =
  let c = ref 0 in
  (fun () ->
    let adr = !c in
    c := adr + 1;
    { contents = Nil; adr })

let address t = t.adr

let add : type a. a table -> cell -> a -> unit = fun t c a ->
  if Hash.mem t.hi c then (
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
    Hash.add t.hi c)

let rec find_aux : type a. a table -> clist -> a = fun t c ->
  match c with
  | Nil -> raise Not_found
  | Cons(tag,x,r) ->
     match t.eq tag with
     | Eq  -> x
     | Neq -> find_aux t r

let find : type a. a table -> cell -> a = fun t c -> find_aux t c.contents

let rec clear_aux : type a. a table -> clist -> clist = fun t l ->
  match l with
  | Nil -> Nil
  | Cons(tag,x,r) ->
     match t.eq tag with
     | Eq -> r
     | Neq -> Cons(tag,x,clear_aux t r)

let remove : type a. a table -> cell -> unit = fun t c ->
  c.contents <- clear_aux t c.contents;
  Hash.remove t.hi c

let clear : type a. a table -> unit = fun t ->
  Hash.iter (fun c -> c.contents <- clear_aux t c.contents) t.hi;
  Hash.clear t.hi

let create_table : type a.int -> a table = fun size ->
  let module M = struct type _ tag += T : a tag end in
  let eq : type b.b tag -> (a, b) eq =
    function M.T -> Eq | _ -> Neq
  in
  let res = {id = M.T; eq; hi=Hash.create size} in
  Gc.finalise clear res;
  res
