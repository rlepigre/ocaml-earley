(** Standard eq-type. *)
type ('a,'b) eq =
  | Y : ('a,'a) eq
  | N : ('a,'b) eq

(** GADT to represent types in the syntax (extended when needed). *)
type _ tag = ..

module Make(V:sig type ('a,'b) elt end) = struct
  include V

  (** Non-uniform list (containing elements of possibly different types). *)
  type 'b nu_list =
    | Cons : 'a tag * ('a,'b) elt * 'b nu_list -> 'b nu_list
    | Nil  : 'b nu_list

  (** Actual container. *)
  type 'b container =
    { mutable data : 'b nu_list (** Contents for each table. *)
    ;         uid  : int        (** Unique identifier.     *) }

  (** counter outside because of value restriction *)
  let counter = ref (-1)

  (** Creation function for containers. *)
  let create : unit -> 'b container =
    fun () -> incr counter; {data = Nil; uid = !counter}

  (** Obtain the UID of a container. *)
  let address : 'b container -> int = fun c -> c.uid

  (** unboxed mandatory for weak hashtbl to work, 4.04.0 only
      we use Obj until 4.04.0 is more spreaded *)
  (* type any = C : 'b container -> any [@@unboxed] *)
  type any = Obj.t container
  let cast : 'b container -> any = Obj.magic

  (** Weak hash-tables of containers. *)
  module W =
    Weak.Make(
        struct
          type t = any
          let hash c = c.uid
          let equal c1 c2 = c1.uid = c2.uid
        end)

  (** Container table. *)
  type 'a table =
    { tag  : 'a tag                   (** Unique tag for this table.   *)
    ; eq   : 'b. 'b tag -> ('a,'b) eq (** Equality to the table's tag. *)
    ; htbl : W.t                      (** Contents of the table.       *) }

  (** Insert a new value associated to the given table and container. If a
    value is already pre sent, it is overwriten. *)
  let add : type a b. a table -> b container -> (a, b) elt -> unit =
    fun tab c v ->
    if W.mem tab.htbl (cast c) then
      begin
        let rec fn = function
          | Nil           -> assert false
          | Cons(t, w, r) ->
             match tab.eq t with
             | Y -> Cons(t, v, r)
             | N -> Cons(t, w, fn r)
        in
        c.data <- fn c.data
      end
    else
      begin
        c.data <- Cons(tab.tag, v, c.data);
        W.add tab.htbl (cast c)
      end

  (* Find the value associated to the given table and container. *)
  let find : type a b. a table -> b container -> (a, b) elt =
    let rec find : type a. a table -> b nu_list -> (a, b) elt = fun tab c ->
      match c with
      | Nil         -> raise Not_found
      | Cons(t,v,r) -> match tab.eq t with Y -> v | N -> find tab r
    in
    fun tab c -> find tab c.data

  (** Removes the given table from the given list. *)
  let rec remove_table : type a b. a table -> b nu_list -> b nu_list =
    fun tab l ->
    match l with
    | Nil           -> Nil
    | Cons(t, v, r) ->
       match tab.eq t with
       | Y -> r
       | N -> Cons(t, v, remove_table tab r)

  (** Remove the given table from the given container. *)
  let remove : type a b. a table -> b container -> unit = fun tab c ->
    c.data <- remove_table tab c.data;
    W.remove tab.htbl (cast c)

  let clear : type a. a table -> unit = fun tab ->
    W.iter (fun c -> c.data <- remove_table tab c.data) tab.htbl;
    W.clear tab.htbl

  let create_table : type a. int -> a table = fun size ->
    let module M = struct type _ tag += T : a tag end in
    let eq : type b. b tag -> (a, b) eq = function M.T -> Y | _ -> N in
    let res = { tag  = M.T ; eq ; htbl = W.create size } in
    Gc.finalise clear res;
    res

  type 'a iter = { f : 'b.('a, 'b) elt -> unit }

  let iter : type a. a iter -> a table -> unit = fun f tab ->
    let rec fn : Obj.t nu_list -> unit = function
      | Nil -> ()
      | Cons(t,v,r) ->
         begin
           match tab.eq t with
           | Y -> f.f v;
           | N -> ()
         end;
         fn r
    in
    W.iter (fun c -> fn c.data) tab.htbl

  type ('a,'c) fold = { f : 'b.('a, 'b) elt -> 'c -> 'c }

  let fold : type a c. (a, c) fold -> a table -> c -> c = fun f tab acc ->
    let rec fn :  Obj.t nu_list -> c -> c = fun l acc ->
      match l with
      | Nil -> acc
      | Cons(t,v,r) ->
         let acc =
           match tab.eq t with
           | Y -> f.f v acc;
           | N -> acc
         in
         fn r acc
    in
    W.fold (fun c acc -> fn c.data acc) tab.htbl acc

end

module type Param = sig
  type 'a table
  type 'b container
  type ('a, 'b) elt
  val create : unit -> 'b container
  val create_table : int -> 'a table
  val address : 'b container -> int
  val add : 'a table -> 'b container -> ('a, 'b) elt -> unit
  val find : 'a table -> 'b container -> ('a, 'b) elt
  val remove : 'a table -> 'b container -> unit
  val clear : 'a table -> unit
  type 'a iter = { f : 'b.('a, 'b) elt -> unit }
  val iter : 'a iter -> 'a table -> unit
  type ('a,'c) fold = { f : 'b.('a, 'b) elt -> 'c -> 'c }
  val fold : ('a, 'c) fold -> 'a table -> 'c -> 'c
end

type ('a, 'b) el = 'a

include Make(struct type ('a, 'b) elt = ('a, 'b) el end)

(** Exported name for [container]. *)
type t = unit container

(* This does not work !
let iter : type a.(a -> unit) -> a table -> unit =
  fun f tabl ->
    iter { f = (let f : type b.(a, b) el -> unit = f in f) } tab
*)
