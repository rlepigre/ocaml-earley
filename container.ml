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

  type any = C : 'b container -> any

  (** Weak hash-tables of containers. *)
  module W =
    Weak.Make(
        struct
          type t = any
          let hash (C c) = c.uid
          let equal (C c1) (C c2) = c1.uid = c2.uid
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
    if W.mem tab.htbl (C c) then
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
        W.add tab.htbl (C c)
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
    W.remove tab.htbl (C c)

  let clear : type a. a table -> unit = fun tab ->
    W.iter (fun (C c) -> c.data <- remove_table tab c.data) tab.htbl;
    W.clear tab.htbl

  let create_table : type a. int -> a table = fun size ->
    let module M = struct type _ tag += T : a tag end in
    let eq : type b. b tag -> (a, b) eq = function M.T -> Y | _ -> N in
                  let res = { tag  = M.T ; eq ; htbl = W.create size } in
                  Gc.finalise clear res; res
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
end

include Make(struct type ('a, 'b) elt = 'a end)

(** Exported name for [container]. *)
type t = unit container
