open Asttypes
open Docstrings
open Parsetree
open Astextra

let not_supported _loc =
  failwith "Syntax not supported in this version of OCaml"

type 'a with_loc = 'a Location.loc
type loc = Location.t

type lid = Longident.t with_loc
type str = string with_loc
type attrs = attribute list

let default_loc = Ast_helper.default_loc
let with_default_loc = Ast_helper.with_default_loc
 
module Const = Ast_helper.Const

module Attr =
  struct
    let mk ?(loc = !default_loc) id payload = (id, payload)
  end

module Typ = Ast_helper.Typ
module Pat = Ast_helper.Pat

module Exp =
  struct
    include Ast_helper.Exp

    let open_ ?loc ?(attrs = []) od e =
      let lid =
        let mexp = od.popen_expr in
        match mexp.pmod_desc with
        | Pmod_ident lid -> lid
        | _              -> not_supported loc
      in
      mk ?loc (Pexp_open(od.popen_override, lid, e))

    let letop ?loc ?attrs _ _ _ = not_supported loc
    let binding_op _ _ _ loc = not_supported loc
  end

module Val = Ast_helper.Val
module Type = Ast_helper.Type

module Te =
  struct
    include Ast_helper.Te

    let mk ?loc:_ ?attrs ?docs ?params ?priv path constructors =
      mk ?attrs ?docs ?params ?priv path constructors

    let mk_exception ?(loc = !default_loc) ?(attrs = [])
        ?(docs = empty_docs) constructor =
      { ptyexn_constructor = constructor
      ; ptyexn_loc = loc
      ; ptyexn_attributes = add_docs_attrs docs attrs }
  end

module Mty = Ast_helper.Mty
module Mod = Ast_helper.Mod

module Sig =
  struct
    include Ast_helper.Sig

    let type_subst ?(loc = !default_loc) _ =
      not_supported loc

    let exception_ ?loc a =
      mk ?loc (Psig_exception a.ptyexn_constructor)

    let mod_subst ?loc _ =
      not_supported loc
  end

module Str =
  struct
    include Ast_helper.Str

    let exception_ ?loc a =
      mk ?loc (Pstr_exception a.ptyexn_constructor)

    let open_ ?loc od =
      let lid =
        let mexp = od.popen_expr in
        match mexp.pmod_desc with
        | Pmod_ident lid -> lid
        | _              -> not_supported loc
      in
      let od =
        { popen_lid = lid
        ; popen_override = od.popen_override
        ; popen_loc = od.popen_loc
        ; popen_attributes = od.popen_attributes }
      in
      mk ?loc (Pstr_open od)
  end

module Md = Ast_helper.Md

module Ms =
  struct
    let mk ?loc ?attrs ?docs ?text _ _ =
      not_supported loc
  end

module Mtd = Ast_helper.Mtd
module Mb = Ast_helper.Mb

module Opn =
  struct
    let mk ?(loc = !default_loc) ?(attrs = []) ?(docs = empty_docs)
           ?(override = Fresh) expr =
      { popen_expr = expr
      ; popen_override = override
      ; popen_loc = loc
      ; popen_attributes = add_docs_attrs docs attrs }
  end

module Incl = Ast_helper.Incl
module Vb = Ast_helper.Vb

module Cty =
  struct
    include Ast_helper.Cty

    let open_ ?loc ?attrs (od : open_description) cty =
      open_ ?loc ?attrs od.popen_override od.popen_lid cty
  end

module Ctf = Ast_helper.Ctf

module Cl =
  struct
    include Ast_helper.Cl

    let open_ ?loc ?attrs (od : open_description) cle =
      open_ ?loc ?attrs od.popen_override od.popen_lid cle
  end

module Cf = Ast_helper.Cf
module Ci = Ast_helper.Ci
module Csig = Ast_helper.Csig
module Cstr = Ast_helper.Cstr

module Rf =
  struct
    let mk ?loc ?attrs _ =
      not_supported loc

    let tag ?loc ?attrs _ _ _ =
      not_supported loc

    let inherit_ ?loc _ =
      not_supported loc
  end

module Of =
  struct
    let mk ?loc ?attrs _ =
      not_supported loc

    let tag ?loc ?attrs _ _ =
      not_supported loc

    let inherit_ ?loc _ =
      not_supported loc
  end
