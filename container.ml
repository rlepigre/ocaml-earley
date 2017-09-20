(** Standard eq-type. *)
type ('a,'b) eq =
  | Y : ('a,'a) eq
  | N : ('a,'b) eq

(** GADT to represent types in the syntax (extended when needed). *)
type _ tag = ..

(** Non-uniform list (containing elements of possibly different types). *)
type nu_list =
  | Cons : 'a tag * 'a * nu_list -> nu_list
  | Nil  :                          nu_list

(** Actual container. *)
type container =
  { mutable data : nu_list (** Contents of each type. *)
  ;         uid  : int     (** Unique identifier.     *) }

(** Creation function for containers. *)
let create : unit -> container =
  let counter = ref (-1) in
  fun () -> incr counter; {data = Nil; uid = !counter}

(** Obtain the UID of a container. *)
let address : container -> int = fun c -> c.uid

(** Weak hash-tables of containers. *)
module W = Weak.Make(
  struct
    type t = container
    let hash c = c.uid
    let equal c1 c2 = c1 == c2 (* FIXME why not [c1.uid = c2.uid]? *)
  end)

(** Exported name for [container]. *)
type t = container

(** Container table. *)
type 'a table =
  { tag  : 'a tag                   (** Unique tag for this table.   *)
  ; eq   : 'b. 'b tag -> ('a,'b) eq (** Equality to the table's tag. *)
  ; htbl : W.t                      (** Contents of the table.       *) }

(** Insert a new value associated to the given table and container. If a
    value is already present, it is overwriten. *)
let add : type a. a table -> container -> a -> unit = fun tab c v ->
  if W.mem tab.htbl c then
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
      W.add tab.htbl c
    end

(* Find the value associated to the given table and container. *)
let find : type a. a table -> container -> a =
  let rec find : type a. a table -> nu_list -> a = fun tab c ->
    match c with
    | Nil         -> raise Not_found
    | Cons(t,v,r) -> match tab.eq t with Y -> v | N -> find tab r
  in
  fun tab c -> find tab c.data

(** Removes the given table from the given list. *)
let rec remove_table : type a. a table -> nu_list -> nu_list = fun tab l ->
  match l with
  | Nil           -> Nil
  | Cons(t, v, r) ->
      match tab.eq t with
      | Y -> r
      | N -> Cons(t, v, remove_table tab r)

(** Remove the given table from the given container. *)
let remove : type a. a table -> container -> unit = fun tab c ->
  c.data <- remove_table tab c.data;
  W.remove tab.htbl c

let clear : type a. a table -> unit = fun tab ->
  W.iter (fun c -> c.data <- remove_table tab c.data) tab.htbl;
  W.clear tab.htbl

let create_table : type a. int -> a table = fun size ->
  let module M = struct type _ tag += T : a tag end in
  let eq : type b. b tag -> (a, b) eq = function M.T -> Y | _ -> N in
  let res = { tag  = M.T ; eq ; htbl = W.create size } in
  Gc.finalise clear res; res
