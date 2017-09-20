(** This library provide a type [ Container.t ], which can be used as a
    list of polymorphic references.

    Another way to see it, is map with access time in O(N) where
    N is the number of tables! Note: O(1) is possible, but usually
    there are very few table at the same time.

    The typical use case is to have a record with a field of type
    [ Container.t ]. Then when you want to store some information in
    that field of type [ a ], you create with [ Container.create_table ],
    a value of type [ a Container.table ]. The with [ Container.add ]
    and [ Container.find ], you can store value in your field of
    type [ Container.t ] }
 *)

(** Type of a container cell *)
type t

(** Type of a container table. You must create a container table of
    type [ a table ] to store value of type [ a ] in a container
    cell. Many table can have the same type, the value are associated
    to the pair (cell, table), not just to the cell. *)
type 'a table

(** [ create () ] creates a new container cell *)
val create : unit -> t

(** [ add tab cell v ] associates the value v to the pair (tab, cell).
    complexity if O(N) where N is the number of tables with a value
    associated to this cell. *)
val add : 'a table -> t -> 'a -> unit

(** [ remove tab cell ] remove the association (tab, cell). Does
    nothing if there was no such association. *)
val remove : 'a table -> t -> unit

(** [ find tab cell ] return the value associated to (tab, cell).
    raises Not_found if the are no such value *)
val find : 'a table -> t -> 'a

(** [ clear tab ] removed all value associated to a table. *)
val clear : 'a table -> unit

(** [ create_table n ] creates a new table. [ n ] is the initial size
    of the internal hashtable. It should be the expected number of
    cell assigned in this table *)
val create_table : int -> 'a table

(** [ address n ] return a unique id of each cell *)
val address   : t -> int
