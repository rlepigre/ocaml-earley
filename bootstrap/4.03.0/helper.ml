open Asttypes
open Docstrings
open Parsetree
open Astextra

let default_loc = Ast_helper.default_loc
let with_default_loc = Ast_helper.with_default_loc

let build_loc loc =
  match loc with
  | None     -> !default_loc
  | Some loc -> loc

let build_attrs attrs =
  match attrs with
  | None       -> []
  | Some attrs -> attrs

let str_opt_to_string_opt so =
  match so with
  | None   -> None
  | Some s -> Some s.txt

module Const = Ast_helper.Const

module Typ  =
  struct
    include Ast_helper.Typ

    let varify_constructors : str list -> core_type -> core_type =
      fun _ _ ->
        (* TODO is this even useful? *)
        assert false

    let object_ : ?loc:loc -> ?attrs:attrs
        -> (str * Parsetree.attributes * Parsetree.core_type) list
        -> Asttypes.closed_flag -> Parsetree.core_type =
      fun ?loc ?attrs l ->
        let l = List.map (fun (s,a,ct) -> (s.txt,a,ct)) l in
        object_ ~loc:(build_loc loc) ~attrs:(build_attrs attrs) l

    let poly : ?loc:loc -> ?attrs:attrs -> str list -> core_type
        -> core_type =
      fun ?loc ?attrs ss ->
        let ss = List.map (fun s -> s.txt) ss in
        poly ~loc:(build_loc loc) ~attrs:(build_attrs attrs) ss
  end

module Pat  =
  struct
    include Ast_helper.Pat

    let open_ : ?loc:loc -> ?attrs:attrs  -> lid -> pattern -> pattern =
      fun ?loc ?attrs _ _ ->
        (* TODO probably difficult to backport. *)
        assert false
  end

module Exp  =
  struct
    include Ast_helper.Exp

    let send: ?loc:loc -> ?attrs:attrs -> expression -> str -> expression =
      fun ?loc ?attrs e s ->
        send ~loc:(build_loc loc) ~attrs:(build_attrs attrs) e s.txt

    let letexception : ?loc:loc -> ?attrs:attrs -> extension_constructor
        -> expression -> expression =
      fun ?loc ?attrs _ _ ->
        (* TODO can be backported using first-class module. *)
        assert false

    let newtype: ?loc:loc -> ?attrs:attrs -> str -> expression -> expression =
      fun ?loc ?attrs s ->
        newtype ~loc:(build_loc loc) ~attrs:(build_attrs attrs) s.txt
  end

module Val  = Ast_helper.Val
module Type = Ast_helper.Type
module Te   = Ast_helper.Te
module Mty  = Ast_helper.Mty
module Mod  = Ast_helper.Mod
module Sig  = Ast_helper.Sig
module Str  = Ast_helper.Str
module Md   = Ast_helper.Md
module Mtd  = Ast_helper.Mtd
module Mb   = Ast_helper.Mb
module Opn  = Ast_helper.Opn
module Incl = Ast_helper.Incl
module Vb   = Ast_helper.Vb

module Cty  =
  struct
    include Ast_helper.Cty

    let open_ : ?loc:loc -> ?attrs:attrs  -> override_flag ->
                lid -> class_type -> class_type =
      fun ?loc ?attrs _ _ ->
        (* TODO probably difficult to backport. *)
        assert false
  end

module Ctf  =
  struct
    include Ast_helper.Ctf

    let val_ : ?loc:loc -> ?attrs:attrs -> str -> mutable_flag
        -> virtual_flag -> core_type -> class_type_field =
      fun ?loc ?attrs s ->
        val_ ~loc:(build_loc loc) ~attrs:(build_attrs attrs) s.txt

    let method_: ?loc:loc -> ?attrs:attrs -> str -> private_flag
        -> virtual_flag -> core_type -> class_type_field =
      fun ?loc ?attrs s ->
        method_ ~loc:(build_loc loc) ~attrs:(build_attrs attrs) s.txt
  end

module Cf   =
  struct
    include Ast_helper.Cf

    let inherit_: ?loc:loc -> ?attrs:attrs -> override_flag -> class_expr
        -> str option -> class_field =
      fun ?loc ?attrs flag ce so ->
        let so = str_opt_to_string_opt so in
        inherit_ ~loc:(build_loc loc) ~attrs:(build_attrs attrs) flag ce so
  end

module Cl   =
  struct
    include Ast_helper.Cl

    let open_ : ?loc:loc -> ?attrs:attrs -> override_flag -> lid -> class_expr
                -> class_expr =
      fun ?loc ?attrs _ _ ->
        (* TODO probably difficult to backport. *)
        assert false
  end

module Ci   = Ast_helper.Ci
module Csig = Ast_helper.Csig
module Cstr = Ast_helper.Cstr
