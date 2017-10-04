open Asttypes
open Parsetree
open Longident
open Pa_ocaml_prelude
open Pa_lexing
open Helper
type action =
  | Default 
  | Normal of expression 
  | DepSeq of ((expression -> expression) * expression option * expression) 
let occur id e =
  Iter.do_local_ident := ((fun s  -> if s = id then raise Exit));
  (try
     (match e with
      | Default  -> ()
      | Normal e -> Iter.iter_expression e
      | DepSeq (_,e1,e2) ->
          (Iter.iter_option Iter.iter_expression e1; Iter.iter_expression e2));
     false
   with | Exit  -> true)
  
let find_locate () =
  try
    Some
      (Exp.ident
         { txt = (Lident (Sys.getenv "LOCATE")); loc = Location.none })
  with | Not_found  -> None 
let mkpatt _loc (id,p) =
  match (p, (find_locate ())) with
  | (None ,_) -> Pat.var ~loc:_loc { txt = id; loc = _loc }
  | (Some p,None ) ->
      {
        Parsetree.ppat_desc =
          (Parsetree.Ppat_alias
             (p, { Asttypes.txt = id; Asttypes.loc = _loc }));
        Parsetree.ppat_loc = _loc;
        Parsetree.ppat_attributes = []
      }
  | (Some p,Some _) ->
      {
        Parsetree.ppat_desc =
          (Parsetree.Ppat_alias
             ({
                Parsetree.ppat_desc =
                  (Parsetree.Ppat_tuple
                     [{
                        Parsetree.ppat_desc = Parsetree.Ppat_any;
                        Parsetree.ppat_loc = _loc;
                        Parsetree.ppat_attributes = []
                      };
                     p]);
                Parsetree.ppat_loc = _loc;
                Parsetree.ppat_attributes = []
              }, { Asttypes.txt = id; Asttypes.loc = _loc }));
        Parsetree.ppat_loc = _loc;
        Parsetree.ppat_attributes = []
      }
  
let mkpatt' _loc (id,p) =
  match p with
  | None  ->
      {
        Parsetree.ppat_desc =
          (Parsetree.Ppat_var { Asttypes.txt = id; Asttypes.loc = _loc });
        Parsetree.ppat_loc = _loc;
        Parsetree.ppat_attributes = []
      }
  | Some p ->
      {
        Parsetree.ppat_desc =
          (Parsetree.Ppat_alias
             (p, { Asttypes.txt = id; Asttypes.loc = _loc }));
        Parsetree.ppat_loc = _loc;
        Parsetree.ppat_attributes = []
      }
  
let cache_filter = Hashtbl.create 101 
let filter _loc visible r =
  match ((find_locate ()), visible) with
  | (Some f2,true ) ->
      let f =
        {
          Parsetree.pexp_desc =
            (Parsetree.Pexp_fun
               (Asttypes.Nolabel, None,
                 {
                   Parsetree.ppat_desc =
                     (Parsetree.Ppat_var
                        { Asttypes.txt = "x"; Asttypes.loc = _loc });
                   Parsetree.ppat_loc = _loc;
                   Parsetree.ppat_attributes = []
                 },
                 {
                   Parsetree.pexp_desc =
                     (Parsetree.Pexp_fun
                        (Asttypes.Nolabel, None,
                          {
                            Parsetree.ppat_desc =
                              (Parsetree.Ppat_var
                                 { Asttypes.txt = "str"; Asttypes.loc = _loc
                                 });
                            Parsetree.ppat_loc = _loc;
                            Parsetree.ppat_attributes = []
                          },
                          {
                            Parsetree.pexp_desc =
                              (Parsetree.Pexp_fun
                                 (Asttypes.Nolabel, None,
                                   {
                                     Parsetree.ppat_desc =
                                       (Parsetree.Ppat_var
                                          {
                                            Asttypes.txt = "pos";
                                            Asttypes.loc = _loc
                                          });
                                     Parsetree.ppat_loc = _loc;
                                     Parsetree.ppat_attributes = []
                                   },
                                   {
                                     Parsetree.pexp_desc =
                                       (Parsetree.Pexp_fun
                                          (Asttypes.Nolabel, None,
                                            {
                                              Parsetree.ppat_desc =
                                                (Parsetree.Ppat_var
                                                   {
                                                     Asttypes.txt = "str'";
                                                     Asttypes.loc = _loc
                                                   });
                                              Parsetree.ppat_loc = _loc;
                                              Parsetree.ppat_attributes = []
                                            },
                                            {
                                              Parsetree.pexp_desc =
                                                (Parsetree.Pexp_fun
                                                   (Asttypes.Nolabel, None,
                                                     {
                                                       Parsetree.ppat_desc =
                                                         (Parsetree.Ppat_var
                                                            {
                                                              Asttypes.txt =
                                                                "pos'";
                                                              Asttypes.loc =
                                                                _loc
                                                            });
                                                       Parsetree.ppat_loc =
                                                         _loc;
                                                       Parsetree.ppat_attributes
                                                         = []
                                                     },
                                                     {
                                                       Parsetree.pexp_desc =
                                                         (Parsetree.Pexp_tuple
                                                            [{
                                                               Parsetree.pexp_desc
                                                                 =
                                                                 (Parsetree.Pexp_apply
                                                                    (f2,
                                                                    [
                                                                    (Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "str");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    });
                                                                    (Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "pos");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    });
                                                                    (Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "str'");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    });
                                                                    (Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "pos'");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    })]));
                                                               Parsetree.pexp_loc
                                                                 = _loc;
                                                               Parsetree.pexp_attributes
                                                                 = []
                                                             };
                                                            {
                                                              Parsetree.pexp_desc
                                                                =
                                                                (Parsetree.Pexp_ident
                                                                   {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "x");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                   });
                                                              Parsetree.pexp_loc
                                                                = _loc;
                                                              Parsetree.pexp_attributes
                                                                = []
                                                            }]);
                                                       Parsetree.pexp_loc =
                                                         _loc;
                                                       Parsetree.pexp_attributes
                                                         = []
                                                     }));
                                              Parsetree.pexp_loc = _loc;
                                              Parsetree.pexp_attributes = []
                                            }));
                                     Parsetree.pexp_loc = _loc;
                                     Parsetree.pexp_attributes = []
                                   }));
                            Parsetree.pexp_loc = _loc;
                            Parsetree.pexp_attributes = []
                          }));
                   Parsetree.pexp_loc = _loc;
                   Parsetree.pexp_attributes = []
                 }));
          Parsetree.pexp_loc = _loc;
          Parsetree.pexp_attributes = []
        }  in
      (try Hashtbl.find cache_filter (f, r)
       with
       | Not_found  ->
           let res =
             {
               Parsetree.pexp_desc =
                 (Parsetree.Pexp_apply
                    ({
                       Parsetree.pexp_desc =
                         (Parsetree.Pexp_ident
                            {
                              Asttypes.txt =
                                (Longident.Ldot
                                   ((Longident.Lident "Earley"),
                                     "apply_position"));
                              Asttypes.loc = _loc
                            });
                       Parsetree.pexp_loc = _loc;
                       Parsetree.pexp_attributes = []
                     }, [(Asttypes.Nolabel, f); (Asttypes.Nolabel, r)]));
               Parsetree.pexp_loc = _loc;
               Parsetree.pexp_attributes = []
             }  in
           (Hashtbl.add cache_filter (f, r) res; res))
  | _ -> r 
let rec build_action _loc occur_loc ids e =
  let e =
    match ((find_locate ()), occur_loc) with
    | (Some locate2,true ) ->
        {
          Parsetree.pexp_desc =
            (Parsetree.Pexp_fun
               (Asttypes.Nolabel, None,
                 {
                   Parsetree.ppat_desc =
                     (Parsetree.Ppat_var
                        {
                          Asttypes.txt = "__loc__start__buf";
                          Asttypes.loc = _loc
                        });
                   Parsetree.ppat_loc = _loc;
                   Parsetree.ppat_attributes = []
                 },
                 {
                   Parsetree.pexp_desc =
                     (Parsetree.Pexp_fun
                        (Asttypes.Nolabel, None,
                          {
                            Parsetree.ppat_desc =
                              (Parsetree.Ppat_var
                                 {
                                   Asttypes.txt = "__loc__start__pos";
                                   Asttypes.loc = _loc
                                 });
                            Parsetree.ppat_loc = _loc;
                            Parsetree.ppat_attributes = []
                          },
                          {
                            Parsetree.pexp_desc =
                              (Parsetree.Pexp_fun
                                 (Asttypes.Nolabel, None,
                                   {
                                     Parsetree.ppat_desc =
                                       (Parsetree.Ppat_var
                                          {
                                            Asttypes.txt = "__loc__end__buf";
                                            Asttypes.loc = _loc
                                          });
                                     Parsetree.ppat_loc = _loc;
                                     Parsetree.ppat_attributes = []
                                   },
                                   {
                                     Parsetree.pexp_desc =
                                       (Parsetree.Pexp_fun
                                          (Asttypes.Nolabel, None,
                                            {
                                              Parsetree.ppat_desc =
                                                (Parsetree.Ppat_var
                                                   {
                                                     Asttypes.txt =
                                                       "__loc__end__pos";
                                                     Asttypes.loc = _loc
                                                   });
                                              Parsetree.ppat_loc = _loc;
                                              Parsetree.ppat_attributes = []
                                            },
                                            {
                                              Parsetree.pexp_desc =
                                                (Parsetree.Pexp_let
                                                   (Asttypes.Nonrecursive,
                                                     [{
                                                        Parsetree.pvb_pat =
                                                          {
                                                            Parsetree.ppat_desc
                                                              =
                                                              (Parsetree.Ppat_var
                                                                 {
                                                                   Asttypes.txt
                                                                    = "_loc";
                                                                   Asttypes.loc
                                                                    = _loc
                                                                 });
                                                            Parsetree.ppat_loc
                                                              = _loc;
                                                            Parsetree.ppat_attributes
                                                              = []
                                                          };
                                                        Parsetree.pvb_expr =
                                                          {
                                                            Parsetree.pexp_desc
                                                              =
                                                              (Parsetree.Pexp_apply
                                                                 (locate2,
                                                                   [(Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "__loc__start__buf");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    });
                                                                   (Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "__loc__start__pos");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    });
                                                                   (Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "__loc__end__buf");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    });
                                                                   (Asttypes.Nolabel,
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "__loc__end__pos");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    })]));
                                                            Parsetree.pexp_loc
                                                              = _loc;
                                                            Parsetree.pexp_attributes
                                                              = []
                                                          };
                                                        Parsetree.pvb_attributes
                                                          = [];
                                                        Parsetree.pvb_loc =
                                                          _loc
                                                      }], e));
                                              Parsetree.pexp_loc = _loc;
                                              Parsetree.pexp_attributes = []
                                            }));
                                     Parsetree.pexp_loc = _loc;
                                     Parsetree.pexp_attributes = []
                                   }));
                            Parsetree.pexp_loc = _loc;
                            Parsetree.pexp_attributes = []
                          }));
                   Parsetree.pexp_loc = _loc;
                   Parsetree.pexp_attributes = []
                 }));
          Parsetree.pexp_loc = _loc;
          Parsetree.pexp_attributes = []
        }
    | _ -> e  in
  List.fold_left
    (fun e  ->
       fun ((id,x),visible)  ->
         match ((find_locate ()), visible) with
         | (Some _,true ) ->
             {
               Parsetree.pexp_desc =
                 (Parsetree.Pexp_fun
                    (Asttypes.Nolabel, None, (mkpatt _loc (id, x)),
                      {
                        Parsetree.pexp_desc =
                          (Parsetree.Pexp_let
                             (Asttypes.Nonrecursive,
                               [{
                                  Parsetree.pvb_pat =
                                    {
                                      Parsetree.ppat_desc =
                                        (Parsetree.Ppat_tuple
                                           [{
                                              Parsetree.ppat_desc =
                                                (Parsetree.Ppat_var
                                                   {
                                                     Asttypes.txt =
                                                       ("_loc_" ^ id);
                                                     Asttypes.loc = _loc
                                                   });
                                              Parsetree.ppat_loc = _loc;
                                              Parsetree.ppat_attributes = []
                                            };
                                           {
                                             Parsetree.ppat_desc =
                                               (Parsetree.Ppat_var
                                                  {
                                                    Asttypes.txt = id;
                                                    Asttypes.loc = _loc
                                                  });
                                             Parsetree.ppat_loc = _loc;
                                             Parsetree.ppat_attributes = []
                                           }]);
                                      Parsetree.ppat_loc = _loc;
                                      Parsetree.ppat_attributes = []
                                    };
                                  Parsetree.pvb_expr =
                                    {
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Lident id);
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    };
                                  Parsetree.pvb_attributes = [];
                                  Parsetree.pvb_loc = _loc
                                }], e));
                        Parsetree.pexp_loc = _loc;
                        Parsetree.pexp_attributes = []
                      }));
               Parsetree.pexp_loc = _loc;
               Parsetree.pexp_attributes = []
             }
         | _ ->
             {
               Parsetree.pexp_desc =
                 (Parsetree.Pexp_fun
                    (Asttypes.Nolabel, None, (mkpatt' _loc (id, x)), e));
               Parsetree.pexp_loc = _loc;
               Parsetree.pexp_attributes = []
             }) e (List.rev ids)
  
let apply_option _loc opt visible e =
  let fn e f d =
    match d with
    | None  ->
        {
          Parsetree.pexp_desc =
            (Parsetree.Pexp_apply
               ({
                  Parsetree.pexp_desc =
                    (Parsetree.Pexp_ident
                       {
                         Asttypes.txt =
                           (Longident.Ldot ((Longident.Lident "Earley"), f));
                         Asttypes.loc = _loc
                       });
                  Parsetree.pexp_loc = _loc;
                  Parsetree.pexp_attributes = []
                },
                 [(Asttypes.Nolabel,
                    {
                      Parsetree.pexp_desc =
                        (Parsetree.Pexp_construct
                           ({
                              Asttypes.txt = (Longident.Lident "None");
                              Asttypes.loc = _loc
                            }, None));
                      Parsetree.pexp_loc = _loc;
                      Parsetree.pexp_attributes = []
                    });
                 (Asttypes.Nolabel,
                   {
                     Parsetree.pexp_desc =
                       (Parsetree.Pexp_apply
                          ({
                             Parsetree.pexp_desc =
                               (Parsetree.Pexp_ident
                                  {
                                    Asttypes.txt =
                                      (Longident.Ldot
                                         ((Longident.Lident "Earley"),
                                           "apply"));
                                    Asttypes.loc = _loc
                                  });
                             Parsetree.pexp_loc = _loc;
                             Parsetree.pexp_attributes = []
                           },
                            [(Asttypes.Nolabel,
                               {
                                 Parsetree.pexp_desc =
                                   (Parsetree.Pexp_fun
                                      (Asttypes.Nolabel, None,
                                        {
                                          Parsetree.ppat_desc =
                                            (Parsetree.Ppat_var
                                               {
                                                 Asttypes.txt = "x";
                                                 Asttypes.loc = _loc
                                               });
                                          Parsetree.ppat_loc = _loc;
                                          Parsetree.ppat_attributes = []
                                        },
                                        {
                                          Parsetree.pexp_desc =
                                            (Parsetree.Pexp_construct
                                               ({
                                                  Asttypes.txt =
                                                    (Longident.Lident "Some");
                                                  Asttypes.loc = _loc
                                                },
                                                 (Some
                                                    {
                                                      Parsetree.pexp_desc =
                                                        (Parsetree.Pexp_ident
                                                           {
                                                             Asttypes.txt =
                                                               (Longident.Lident
                                                                  "x");
                                                             Asttypes.loc =
                                                               _loc
                                                           });
                                                      Parsetree.pexp_loc =
                                                        _loc;
                                                      Parsetree.pexp_attributes
                                                        = []
                                                    })));
                                          Parsetree.pexp_loc = _loc;
                                          Parsetree.pexp_attributes = []
                                        }));
                                 Parsetree.pexp_loc = _loc;
                                 Parsetree.pexp_attributes = []
                               });
                            (Asttypes.Nolabel, e)]));
                     Parsetree.pexp_loc = _loc;
                     Parsetree.pexp_attributes = []
                   })]));
          Parsetree.pexp_loc = _loc;
          Parsetree.pexp_attributes = []
        }
    | Some d ->
        {
          Parsetree.pexp_desc =
            (Parsetree.Pexp_apply
               ({
                  Parsetree.pexp_desc =
                    (Parsetree.Pexp_ident
                       {
                         Asttypes.txt =
                           (Longident.Ldot ((Longident.Lident "Earley"), f));
                         Asttypes.loc = _loc
                       });
                  Parsetree.pexp_loc = _loc;
                  Parsetree.pexp_attributes = []
                }, [(Asttypes.Nolabel, d); (Asttypes.Nolabel, e)]));
          Parsetree.pexp_loc = _loc;
          Parsetree.pexp_attributes = []
        }
     in
  let gn e f d =
    match d with
    | None  ->
        {
          Parsetree.pexp_desc =
            (Parsetree.Pexp_apply
               ({
                  Parsetree.pexp_desc =
                    (Parsetree.Pexp_ident
                       {
                         Asttypes.txt =
                           (Longident.Ldot
                              ((Longident.Lident "Earley"), "apply"));
                         Asttypes.loc = _loc
                       });
                  Parsetree.pexp_loc = _loc;
                  Parsetree.pexp_attributes = []
                },
                 [(Asttypes.Nolabel,
                    {
                      Parsetree.pexp_desc =
                        (Parsetree.Pexp_ident
                           {
                             Asttypes.txt =
                               (Longident.Ldot
                                  ((Longident.Lident "List"), "rev"));
                             Asttypes.loc = _loc
                           });
                      Parsetree.pexp_loc = _loc;
                      Parsetree.pexp_attributes = []
                    });
                 (Asttypes.Nolabel,
                   {
                     Parsetree.pexp_desc =
                       (Parsetree.Pexp_apply
                          ({
                             Parsetree.pexp_desc =
                               (Parsetree.Pexp_ident
                                  {
                                    Asttypes.txt =
                                      (Longident.Ldot
                                         ((Longident.Lident "Earley"), f));
                                    Asttypes.loc = _loc
                                  });
                             Parsetree.pexp_loc = _loc;
                             Parsetree.pexp_attributes = []
                           },
                            [(Asttypes.Nolabel,
                               {
                                 Parsetree.pexp_desc =
                                   (Parsetree.Pexp_construct
                                      ({
                                         Asttypes.txt =
                                           (Longident.Lident "[]");
                                         Asttypes.loc = _loc
                                       }, None));
                                 Parsetree.pexp_loc = _loc;
                                 Parsetree.pexp_attributes = []
                               });
                            (Asttypes.Nolabel,
                              {
                                Parsetree.pexp_desc =
                                  (Parsetree.Pexp_apply
                                     ({
                                        Parsetree.pexp_desc =
                                          (Parsetree.Pexp_ident
                                             {
                                               Asttypes.txt =
                                                 (Longident.Ldot
                                                    ((Longident.Lident
                                                        "Earley"), "apply"));
                                               Asttypes.loc = _loc
                                             });
                                        Parsetree.pexp_loc = _loc;
                                        Parsetree.pexp_attributes = []
                                      },
                                       [(Asttypes.Nolabel,
                                          {
                                            Parsetree.pexp_desc =
                                              (Parsetree.Pexp_fun
                                                 (Asttypes.Nolabel, None,
                                                   {
                                                     Parsetree.ppat_desc =
                                                       (Parsetree.Ppat_var
                                                          {
                                                            Asttypes.txt =
                                                              "x";
                                                            Asttypes.loc =
                                                              _loc
                                                          });
                                                     Parsetree.ppat_loc =
                                                       _loc;
                                                     Parsetree.ppat_attributes
                                                       = []
                                                   },
                                                   {
                                                     Parsetree.pexp_desc =
                                                       (Parsetree.Pexp_fun
                                                          (Asttypes.Nolabel,
                                                            None,
                                                            {
                                                              Parsetree.ppat_desc
                                                                =
                                                                (Parsetree.Ppat_var
                                                                   {
                                                                    Asttypes.txt
                                                                    = "y";
                                                                    Asttypes.loc
                                                                    = _loc
                                                                   });
                                                              Parsetree.ppat_loc
                                                                = _loc;
                                                              Parsetree.ppat_attributes
                                                                = []
                                                            },
                                                            {
                                                              Parsetree.pexp_desc
                                                                =
                                                                (Parsetree.Pexp_construct
                                                                   ({
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "::");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    },
                                                                    (Some
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_tuple
                                                                    [
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "x");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    };
                                                                    {
                                                                    Parsetree.pexp_desc
                                                                    =
                                                                    (Parsetree.Pexp_ident
                                                                    {
                                                                    Asttypes.txt
                                                                    =
                                                                    (Longident.Lident
                                                                    "y");
                                                                    Asttypes.loc
                                                                    = _loc
                                                                    });
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    }]);
                                                                    Parsetree.pexp_loc
                                                                    = _loc;
                                                                    Parsetree.pexp_attributes
                                                                    = []
                                                                    })));
                                                              Parsetree.pexp_loc
                                                                = _loc;
                                                              Parsetree.pexp_attributes
                                                                = []
                                                            }));
                                                     Parsetree.pexp_loc =
                                                       _loc;
                                                     Parsetree.pexp_attributes
                                                       = []
                                                   }));
                                            Parsetree.pexp_loc = _loc;
                                            Parsetree.pexp_attributes = []
                                          });
                                       (Asttypes.Nolabel, e)]));
                                Parsetree.pexp_loc = _loc;
                                Parsetree.pexp_attributes = []
                              })]));
                     Parsetree.pexp_loc = _loc;
                     Parsetree.pexp_attributes = []
                   })]));
          Parsetree.pexp_loc = _loc;
          Parsetree.pexp_attributes = []
        }
    | Some d ->
        {
          Parsetree.pexp_desc =
            (Parsetree.Pexp_apply
               ({
                  Parsetree.pexp_desc =
                    (Parsetree.Pexp_ident
                       {
                         Asttypes.txt =
                           (Longident.Ldot ((Longident.Lident "Earley"), f));
                         Asttypes.loc = _loc
                       });
                  Parsetree.pexp_loc = _loc;
                  Parsetree.pexp_attributes = []
                }, [(Asttypes.Nolabel, d); (Asttypes.Nolabel, e)]));
          Parsetree.pexp_loc = _loc;
          Parsetree.pexp_attributes = []
        }
     in
  let kn e =
    function
    | None  -> e
    | Some _ ->
        {
          Parsetree.pexp_desc =
            (Parsetree.Pexp_apply
               ({
                  Parsetree.pexp_desc =
                    (Parsetree.Pexp_ident
                       {
                         Asttypes.txt =
                           (Longident.Ldot
                              ((Longident.Lident "Earley"), "greedy"));
                         Asttypes.loc = _loc
                       });
                  Parsetree.pexp_loc = _loc;
                  Parsetree.pexp_attributes = []
                }, [(Asttypes.Nolabel, e)]));
          Parsetree.pexp_loc = _loc;
          Parsetree.pexp_attributes = []
        }
     in
  filter _loc visible
    (match opt with
     | `Once -> e
     | `Option (d,g) -> kn (fn e "option" d) g
     | `Greedy ->
         {
           Parsetree.pexp_desc =
             (Parsetree.Pexp_apply
                ({
                   Parsetree.pexp_desc =
                     (Parsetree.Pexp_ident
                        {
                          Asttypes.txt =
                            (Longident.Ldot
                               ((Longident.Lident "Earley"), "greedy"));
                          Asttypes.loc = _loc
                        });
                   Parsetree.pexp_loc = _loc;
                   Parsetree.pexp_attributes = []
                 }, [(Asttypes.Nolabel, e)]));
           Parsetree.pexp_loc = _loc;
           Parsetree.pexp_attributes = []
         }
     | `Fixpoint (d,g) -> kn (gn e "fixpoint" d) g
     | `Fixpoint1 (d,g) -> kn (gn e "fixpoint1" d) g)
  
let default_action _loc l =
  let l =
    List.filter
      (function | `Normal (("_",_),false ,_,_,_) -> false | _ -> true) l
     in
  let l =
    List.map
      (function
       | `Normal ((id,_),_,_,_,_) ->
           {
             Parsetree.pexp_desc =
               (Parsetree.Pexp_ident
                  { Asttypes.txt = (Longident.Lident id); Asttypes.loc = _loc
                  });
             Parsetree.pexp_loc = _loc;
             Parsetree.pexp_attributes = []
           }
       | _ -> assert false) l
     in
  Pa_ast.exp_tuple _loc l 
let from_opt ov d = match ov with | None  -> d | Some v -> v 
let dash =
  let fn str pos =
    let (c,str',pos') = Input.read str pos  in
    if c = '-'
    then
      let (c',_,_) = Input.read str' pos'  in
      (if c' = '>' then Earley.give_up () else ((), str', pos'))
    else Earley.give_up ()  in
  Earley.black_box fn (Charset.singleton '-') false "-" 
module Ext(In:Extension) =
  struct
    include In
    let expr_arg = expression_lvl (NoMatch, (next_exp App)) 
    let build_rule (_loc,occur_loc,def,l,condition,action) =
      let (iter,action) =
        match action with
        | Normal a -> (false, a)
        | Default  -> (false, (default_action _loc l))
        | DepSeq (def,cond,a) ->
            (true,
              ((match cond with
                | None  -> def a
                | Some cond ->
                    def
                      {
                        Parsetree.pexp_desc =
                          (Parsetree.Pexp_ifthenelse
                             (cond, a,
                               (Some
                                  {
                                    Parsetree.pexp_desc =
                                      (Parsetree.Pexp_apply
                                         ({
                                            Parsetree.pexp_desc =
                                              (Parsetree.Pexp_ident
                                                 {
                                                   Asttypes.txt =
                                                     (Longident.Ldot
                                                        ((Longident.Lident
                                                            "Earley"),
                                                          "fail"));
                                                   Asttypes.loc = _loc
                                                 });
                                            Parsetree.pexp_loc = _loc;
                                            Parsetree.pexp_attributes = []
                                          },
                                           [(Asttypes.Nolabel,
                                              {
                                                Parsetree.pexp_desc =
                                                  (Parsetree.Pexp_construct
                                                     ({
                                                        Asttypes.txt =
                                                          (Longident.Lident
                                                             "()");
                                                        Asttypes.loc = _loc
                                                      }, None));
                                                Parsetree.pexp_loc = _loc;
                                                Parsetree.pexp_attributes =
                                                  []
                                              })]));
                                    Parsetree.pexp_loc = _loc;
                                    Parsetree.pexp_attributes = []
                                  })));
                        Parsetree.pexp_loc = _loc;
                        Parsetree.pexp_attributes = []
                      })))
         in
      let rec fn first ids l =
        match l with
        | [] -> assert false
        | (`Normal (id,_,e,opt,occur_loc_id))::[] ->
            let e = apply_option _loc opt occur_loc_id e  in
            let f =
              match ((find_locate ()), (first && occur_loc)) with
              | (Some _,true ) -> "apply_position"
              | _ -> "apply"  in
            (match action.pexp_desc with
             | Pexp_ident { txt = Lident id' } when
                 ((fst id) = id') && (f = "apply") -> e
             | _ ->
                 let a =
                   build_action _loc occur_loc ((id, occur_loc_id) :: ids)
                     action
                    in
                 {
                   Parsetree.pexp_desc =
                     (Parsetree.Pexp_apply
                        ({
                           Parsetree.pexp_desc =
                             (Parsetree.Pexp_ident
                                {
                                  Asttypes.txt =
                                    (Longident.Ldot
                                       ((Longident.Lident "Earley"), f));
                                  Asttypes.loc = _loc
                                });
                           Parsetree.pexp_loc = _loc;
                           Parsetree.pexp_attributes = []
                         }, [(Asttypes.Nolabel, a); (Asttypes.Nolabel, e)]));
                   Parsetree.pexp_loc = _loc;
                   Parsetree.pexp_attributes = []
                 })
        | (`Normal (id,_,e,opt,occur_loc_id))::(`Normal
                                                  (id',_,e',opt',occur_loc_id'))::[]
            ->
            let e = apply_option _loc opt occur_loc_id e  in
            let e' = apply_option _loc opt' occur_loc_id' e'  in
            let f =
              match ((find_locate ()), (first && occur_loc)) with
              | (Some _,true ) -> "sequence_position"
              | _ -> "sequence"  in
            let a =
              build_action _loc occur_loc ((id, occur_loc_id) ::
                (id', occur_loc_id') :: ids) action
               in
            {
              Parsetree.pexp_desc =
                (Parsetree.Pexp_apply
                   ({
                      Parsetree.pexp_desc =
                        (Parsetree.Pexp_ident
                           {
                             Asttypes.txt =
                               (Longident.Ldot
                                  ((Longident.Lident "Earley"), f));
                             Asttypes.loc = _loc
                           });
                      Parsetree.pexp_loc = _loc;
                      Parsetree.pexp_attributes = []
                    },
                     [(Asttypes.Nolabel, e);
                     (Asttypes.Nolabel, e');
                     (Asttypes.Nolabel, a)]));
              Parsetree.pexp_loc = _loc;
              Parsetree.pexp_attributes = []
            }
        | (`Normal (id,_,e,opt,occur_loc_id))::ls ->
            let e = apply_option _loc opt occur_loc_id e  in
            let f =
              match ((find_locate ()), (first && occur_loc)) with
              | (Some _,true ) -> "fsequence_position"
              | _ -> "fsequence"  in
            let a = fn false ((id, occur_loc_id) :: ids) ls  in
            {
              Parsetree.pexp_desc =
                (Parsetree.Pexp_apply
                   ({
                      Parsetree.pexp_desc =
                        (Parsetree.Pexp_ident
                           {
                             Asttypes.txt =
                               (Longident.Ldot
                                  ((Longident.Lident "Earley"), f));
                             Asttypes.loc = _loc
                           });
                      Parsetree.pexp_loc = _loc;
                      Parsetree.pexp_attributes = []
                    }, [(Asttypes.Nolabel, e); (Asttypes.Nolabel, a)]));
              Parsetree.pexp_loc = _loc;
              Parsetree.pexp_attributes = []
            }
         in
      let res = fn true [] l  in
      let res =
        if iter
        then
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_apply
                 ({
                    Parsetree.pexp_desc =
                      (Parsetree.Pexp_ident
                         {
                           Asttypes.txt =
                             (Longident.Ldot
                                ((Longident.Lident "Earley"), "iter"));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }, [(Asttypes.Nolabel, res)]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
        else res  in
      (def, condition, res) 
    let apply_def_cond _loc r =
      let (def,cond,e) = build_rule r  in
      match cond with
      | None  -> def e
      | Some c ->
          def
            {
              Parsetree.pexp_desc =
                (Parsetree.Pexp_ifthenelse
                   (c, e,
                     (Some
                        {
                          Parsetree.pexp_desc =
                            (Parsetree.Pexp_apply
                               ({
                                  Parsetree.pexp_desc =
                                    (Parsetree.Pexp_ident
                                       {
                                         Asttypes.txt =
                                           (Longident.Ldot
                                              ((Longident.Lident "Earley"),
                                                "fail"));
                                         Asttypes.loc = _loc
                                       });
                                  Parsetree.pexp_loc = _loc;
                                  Parsetree.pexp_attributes = []
                                },
                                 [(Asttypes.Nolabel,
                                    {
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_construct
                                           ({
                                              Asttypes.txt =
                                                (Longident.Lident "()");
                                              Asttypes.loc = _loc
                                            }, None));
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    })]));
                          Parsetree.pexp_loc = _loc;
                          Parsetree.pexp_attributes = []
                        })));
              Parsetree.pexp_loc = _loc;
              Parsetree.pexp_attributes = []
            }
      
    let apply_def_cond_list _loc r acc =
      let (def,cond,e) = build_rule r  in
      match cond with
      | None  ->
          def
            {
              Parsetree.pexp_desc =
                (Parsetree.Pexp_construct
                   ({
                      Asttypes.txt = (Longident.Lident "::");
                      Asttypes.loc = _loc
                    },
                     (Some
                        {
                          Parsetree.pexp_desc =
                            (Parsetree.Pexp_tuple [e; acc]);
                          Parsetree.pexp_loc = _loc;
                          Parsetree.pexp_attributes = []
                        })));
              Parsetree.pexp_loc = _loc;
              Parsetree.pexp_attributes = []
            }
      | Some c ->
          def
            {
              Parsetree.pexp_desc =
                (Parsetree.Pexp_apply
                   ({
                      Parsetree.pexp_desc =
                        (Parsetree.Pexp_ident
                           {
                             Asttypes.txt = (Longident.Lident "@");
                             Asttypes.loc = _loc
                           });
                      Parsetree.pexp_loc = _loc;
                      Parsetree.pexp_attributes = []
                    },
                     [(Asttypes.Nolabel,
                        {
                          Parsetree.pexp_desc =
                            (Parsetree.Pexp_ifthenelse
                               (c,
                                 {
                                   Parsetree.pexp_desc =
                                     (Parsetree.Pexp_construct
                                        ({
                                           Asttypes.txt =
                                             (Longident.Lident "::");
                                           Asttypes.loc = _loc
                                         },
                                          (Some
                                             {
                                               Parsetree.pexp_desc =
                                                 (Parsetree.Pexp_tuple
                                                    [e;
                                                    {
                                                      Parsetree.pexp_desc =
                                                        (Parsetree.Pexp_construct
                                                           ({
                                                              Asttypes.txt =
                                                                (Longident.Lident
                                                                   "[]");
                                                              Asttypes.loc =
                                                                _loc
                                                            }, None));
                                                      Parsetree.pexp_loc =
                                                        _loc;
                                                      Parsetree.pexp_attributes
                                                        = []
                                                    }]);
                                               Parsetree.pexp_loc = _loc;
                                               Parsetree.pexp_attributes = []
                                             })));
                                   Parsetree.pexp_loc = _loc;
                                   Parsetree.pexp_attributes = []
                                 },
                                 (Some
                                    {
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_construct
                                           ({
                                              Asttypes.txt =
                                                (Longident.Lident "[]");
                                              Asttypes.loc = _loc
                                            }, None));
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    })));
                          Parsetree.pexp_loc = _loc;
                          Parsetree.pexp_attributes = []
                        });
                     (Asttypes.Nolabel, acc)]));
              Parsetree.pexp_loc = _loc;
              Parsetree.pexp_attributes = []
            }
      
    let apply_def_cond_prio _loc arg r acc =
      let (def,cond,e) = build_rule r  in
      match cond with
      | None  ->
          def
            {
              Parsetree.pexp_desc =
                (Parsetree.Pexp_construct
                   ({
                      Asttypes.txt = (Longident.Lident "::");
                      Asttypes.loc = _loc
                    },
                     (Some
                        {
                          Parsetree.pexp_desc =
                            (Parsetree.Pexp_tuple
                               [{
                                  Parsetree.pexp_desc =
                                    (Parsetree.Pexp_tuple
                                       [{
                                          Parsetree.pexp_desc =
                                            (Parsetree.Pexp_fun
                                               (Asttypes.Nolabel, None,
                                                 {
                                                   Parsetree.ppat_desc =
                                                     Parsetree.Ppat_any;
                                                   Parsetree.ppat_loc = _loc;
                                                   Parsetree.ppat_attributes
                                                     = []
                                                 },
                                                 {
                                                   Parsetree.pexp_desc =
                                                     (Parsetree.Pexp_construct
                                                        ({
                                                           Asttypes.txt =
                                                             (Longident.Lident
                                                                "true");
                                                           Asttypes.loc =
                                                             _loc
                                                         }, None));
                                                   Parsetree.pexp_loc = _loc;
                                                   Parsetree.pexp_attributes
                                                     = []
                                                 }));
                                          Parsetree.pexp_loc = _loc;
                                          Parsetree.pexp_attributes = []
                                        };
                                       e]);
                                  Parsetree.pexp_loc = _loc;
                                  Parsetree.pexp_attributes = []
                                };
                               acc]);
                          Parsetree.pexp_loc = _loc;
                          Parsetree.pexp_attributes = []
                        })));
              Parsetree.pexp_loc = _loc;
              Parsetree.pexp_attributes = []
            }
      | Some c ->
          def
            {
              Parsetree.pexp_desc =
                (Parsetree.Pexp_construct
                   ({
                      Asttypes.txt = (Longident.Lident "::");
                      Asttypes.loc = _loc
                    },
                     (Some
                        {
                          Parsetree.pexp_desc =
                            (Parsetree.Pexp_tuple
                               [{
                                  Parsetree.pexp_desc =
                                    (Parsetree.Pexp_tuple
                                       [{
                                          Parsetree.pexp_desc =
                                            (Parsetree.Pexp_fun
                                               (Asttypes.Nolabel, None, arg,
                                                 c));
                                          Parsetree.pexp_loc = _loc;
                                          Parsetree.pexp_attributes = []
                                        };
                                       e]);
                                  Parsetree.pexp_loc = _loc;
                                  Parsetree.pexp_attributes = []
                                };
                               acc]);
                          Parsetree.pexp_loc = _loc;
                          Parsetree.pexp_attributes = []
                        })));
              Parsetree.pexp_loc = _loc;
              Parsetree.pexp_attributes = []
            }
      
    let build_alternatives _loc ls =
      let ls = List.map snd ls  in
      match ls with
      | [] ->
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_apply
                 ({
                    Parsetree.pexp_desc =
                      (Parsetree.Pexp_ident
                         {
                           Asttypes.txt =
                             (Longident.Ldot
                                ((Longident.Lident "Earley"), "fail"));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  },
                   [(Asttypes.Nolabel,
                      {
                        Parsetree.pexp_desc =
                          (Parsetree.Pexp_construct
                             ({
                                Asttypes.txt = (Longident.Lident "()");
                                Asttypes.loc = _loc
                              }, None));
                        Parsetree.pexp_loc = _loc;
                        Parsetree.pexp_attributes = []
                      })]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
      | r::[] -> apply_def_cond _loc r
      | _::_::_ ->
          let l =
            List.fold_right (apply_def_cond_list _loc) ls
              {
                Parsetree.pexp_desc =
                  (Parsetree.Pexp_construct
                     ({
                        Asttypes.txt = (Longident.Lident "[]");
                        Asttypes.loc = _loc
                      }, None));
                Parsetree.pexp_loc = _loc;
                Parsetree.pexp_attributes = []
              }
             in
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_apply
                 ({
                    Parsetree.pexp_desc =
                      (Parsetree.Pexp_ident
                         {
                           Asttypes.txt =
                             (Longident.Ldot
                                ((Longident.Lident "Earley"), "alternatives"));
                           Asttypes.loc = _loc
                         });
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }, [(Asttypes.Nolabel, l)]));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
      
    let build_prio_alternatives _loc arg ls =
      let (l0,l1) = List.partition fst ls  in
      let l0 = List.map snd l0
      
      and l1 = List.map snd l1
       in
      let l1 =
        List.fold_right (apply_def_cond_prio _loc arg) l1
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_construct
                 ({
                    Asttypes.txt = (Longident.Lident "[]");
                    Asttypes.loc = _loc
                  }, None));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
         in
      let l0 =
        List.fold_right (apply_def_cond_list _loc) l0
          {
            Parsetree.pexp_desc =
              (Parsetree.Pexp_construct
                 ({
                    Asttypes.txt = (Longident.Lident "[]");
                    Asttypes.loc = _loc
                  }, None));
            Parsetree.pexp_loc = _loc;
            Parsetree.pexp_attributes = []
          }
         in
      {
        Parsetree.pexp_desc =
          (Parsetree.Pexp_tuple
             [l1;
             {
               Parsetree.pexp_desc =
                 (Parsetree.Pexp_fun (Asttypes.Nolabel, None, arg, l0));
               Parsetree.pexp_loc = _loc;
               Parsetree.pexp_attributes = []
             }]);
        Parsetree.pexp_loc = _loc;
        Parsetree.pexp_attributes = []
      } 
    let build_str_item _loc l =
      let rec fn =
        function
        | [] -> ([], [], [])
        | (`Caml b)::l ->
            let (str1,str2,str3) = fn l  in (str1, str2, (b :: str3))
        | (`Parser (name,args,prio,ty,_loc_r,r))::l ->
            let (str1,str2,str3) = fn l  in
            let pname =
              {
                Parsetree.ppat_desc =
                  (Parsetree.Ppat_var
                     { Asttypes.txt = name; Asttypes.loc = _loc });
                Parsetree.ppat_loc = _loc;
                Parsetree.ppat_attributes = []
              }  in
            let coer f =
              match ty with
              | None  -> f
              | Some ty ->
                  {
                    Parsetree.pexp_desc = (Parsetree.Pexp_constraint (f, ty));
                    Parsetree.pexp_loc = _loc;
                    Parsetree.pexp_attributes = []
                  }
               in
            let args_pat = Pa_ast.pat_tuple _loc args  in
            let (str1,str2) =
              match (args, prio) with
              | ([],None ) ->
                  let r = coer (build_alternatives _loc_r r)  in
                  (([{
                       Parsetree.pstr_desc =
                         (Parsetree.Pstr_value
                            (Asttypes.Nonrecursive,
                              [{
                                 Parsetree.pvb_pat = pname;
                                 Parsetree.pvb_expr =
                                   {
                                     Parsetree.pexp_desc =
                                       (Parsetree.Pexp_apply
                                          ({
                                             Parsetree.pexp_desc =
                                               (Parsetree.Pexp_ident
                                                  {
                                                    Asttypes.txt =
                                                      (Longident.Ldot
                                                         ((Longident.Lident
                                                             "Earley"),
                                                           "declare_grammar"));
                                                    Asttypes.loc = _loc
                                                  });
                                             Parsetree.pexp_loc = _loc;
                                             Parsetree.pexp_attributes = []
                                           },
                                            [(Asttypes.Nolabel,
                                               (Pa_ast.exp_string _loc name))]));
                                     Parsetree.pexp_loc = _loc;
                                     Parsetree.pexp_attributes = []
                                   };
                                 Parsetree.pvb_attributes = [];
                                 Parsetree.pvb_loc = _loc
                               }]));
                       Parsetree.pstr_loc = _loc
                     }] @ str1),
                    ([{
                        Parsetree.pstr_desc =
                          (Parsetree.Pstr_value
                             (Asttypes.Nonrecursive,
                               [{
                                  Parsetree.pvb_pat =
                                    {
                                      Parsetree.ppat_desc =
                                        Parsetree.Ppat_any;
                                      Parsetree.ppat_loc = _loc;
                                      Parsetree.ppat_attributes = []
                                    };
                                  Parsetree.pvb_expr =
                                    {
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_apply
                                           ({
                                              Parsetree.pexp_desc =
                                                (Parsetree.Pexp_ident
                                                   {
                                                     Asttypes.txt =
                                                       (Longident.Ldot
                                                          ((Longident.Lident
                                                              "Earley"),
                                                            "set_grammar"));
                                                     Asttypes.loc = _loc
                                                   });
                                              Parsetree.pexp_loc = _loc;
                                              Parsetree.pexp_attributes = []
                                            },
                                             [(Asttypes.Nolabel,
                                                {
                                                  Parsetree.pexp_desc =
                                                    (Parsetree.Pexp_ident
                                                       {
                                                         Asttypes.txt =
                                                           (Longident.Lident
                                                              name);
                                                         Asttypes.loc = _loc
                                                       });
                                                  Parsetree.pexp_loc = _loc;
                                                  Parsetree.pexp_attributes =
                                                    []
                                                });
                                             (Asttypes.Nolabel, r)]));
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    };
                                  Parsetree.pvb_attributes = [];
                                  Parsetree.pvb_loc = _loc
                                }]));
                        Parsetree.pstr_loc = _loc
                      }] @ str2))
              | (_,None ) ->
                  let r = coer (build_alternatives _loc_r r)  in
                  let set_name = name ^ "__set__grammar"  in
                  (([{
                       Parsetree.pstr_desc =
                         (Parsetree.Pstr_value
                            (Asttypes.Nonrecursive,
                              [{
                                 Parsetree.pvb_pat =
                                   {
                                     Parsetree.ppat_desc =
                                       (Parsetree.Ppat_tuple
                                          [pname;
                                          {
                                            Parsetree.ppat_desc =
                                              (Parsetree.Ppat_var
                                                 {
                                                   Asttypes.txt = set_name;
                                                   Asttypes.loc = _loc
                                                 });
                                            Parsetree.ppat_loc = _loc;
                                            Parsetree.ppat_attributes = []
                                          }]);
                                     Parsetree.ppat_loc = _loc;
                                     Parsetree.ppat_attributes = []
                                   };
                                 Parsetree.pvb_expr =
                                   {
                                     Parsetree.pexp_desc =
                                       (Parsetree.Pexp_apply
                                          ({
                                             Parsetree.pexp_desc =
                                               (Parsetree.Pexp_ident
                                                  {
                                                    Asttypes.txt =
                                                      (Longident.Ldot
                                                         ((Longident.Lident
                                                             "Earley"),
                                                           "grammar_family"));
                                                    Asttypes.loc = _loc
                                                  });
                                             Parsetree.pexp_loc = _loc;
                                             Parsetree.pexp_attributes = []
                                           },
                                            [(Asttypes.Nolabel,
                                               (Pa_ast.exp_string _loc name))]));
                                     Parsetree.pexp_loc = _loc;
                                     Parsetree.pexp_attributes = []
                                   };
                                 Parsetree.pvb_attributes = [];
                                 Parsetree.pvb_loc = _loc
                               }]));
                       Parsetree.pstr_loc = _loc
                     }] @ str1),
                    ([{
                        Parsetree.pstr_desc =
                          (Parsetree.Pstr_value
                             (Asttypes.Nonrecursive,
                               [{
                                  Parsetree.pvb_pat =
                                    {
                                      Parsetree.ppat_desc =
                                        Parsetree.Ppat_any;
                                      Parsetree.ppat_loc = _loc;
                                      Parsetree.ppat_attributes = []
                                    };
                                  Parsetree.pvb_expr =
                                    {
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_apply
                                           ({
                                              Parsetree.pexp_desc =
                                                (Parsetree.Pexp_ident
                                                   {
                                                     Asttypes.txt =
                                                       (Longident.Lident
                                                          set_name);
                                                     Asttypes.loc = _loc
                                                   });
                                              Parsetree.pexp_loc = _loc;
                                              Parsetree.pexp_attributes = []
                                            },
                                             [(Asttypes.Nolabel,
                                                {
                                                  Parsetree.pexp_desc =
                                                    (Parsetree.Pexp_fun
                                                       (Asttypes.Nolabel,
                                                         None, args_pat, r));
                                                  Parsetree.pexp_loc = _loc;
                                                  Parsetree.pexp_attributes =
                                                    []
                                                })]));
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    };
                                  Parsetree.pvb_attributes = [];
                                  Parsetree.pvb_loc = _loc
                                }]));
                        Parsetree.pstr_loc = _loc
                      }] @ str2))
              | ([],Some prio) ->
                  let r = coer (build_prio_alternatives _loc_r prio r)  in
                  let set_name = name ^ "__set__grammar"  in
                  (([{
                       Parsetree.pstr_desc =
                         (Parsetree.Pstr_value
                            (Asttypes.Nonrecursive,
                              [{
                                 Parsetree.pvb_pat =
                                   {
                                     Parsetree.ppat_desc =
                                       (Parsetree.Ppat_tuple
                                          [pname;
                                          {
                                            Parsetree.ppat_desc =
                                              (Parsetree.Ppat_var
                                                 {
                                                   Asttypes.txt = set_name;
                                                   Asttypes.loc = _loc
                                                 });
                                            Parsetree.ppat_loc = _loc;
                                            Parsetree.ppat_attributes = []
                                          }]);
                                     Parsetree.ppat_loc = _loc;
                                     Parsetree.ppat_attributes = []
                                   };
                                 Parsetree.pvb_expr =
                                   {
                                     Parsetree.pexp_desc =
                                       (Parsetree.Pexp_apply
                                          ({
                                             Parsetree.pexp_desc =
                                               (Parsetree.Pexp_ident
                                                  {
                                                    Asttypes.txt =
                                                      (Longident.Ldot
                                                         ((Longident.Lident
                                                             "Earley"),
                                                           "grammar_prio"));
                                                    Asttypes.loc = _loc
                                                  });
                                             Parsetree.pexp_loc = _loc;
                                             Parsetree.pexp_attributes = []
                                           },
                                            [(Asttypes.Nolabel,
                                               (Pa_ast.exp_string _loc name))]));
                                     Parsetree.pexp_loc = _loc;
                                     Parsetree.pexp_attributes = []
                                   };
                                 Parsetree.pvb_attributes = [];
                                 Parsetree.pvb_loc = _loc
                               }]));
                       Parsetree.pstr_loc = _loc
                     }] @ str1),
                    ([{
                        Parsetree.pstr_desc =
                          (Parsetree.Pstr_value
                             (Asttypes.Nonrecursive,
                               [{
                                  Parsetree.pvb_pat =
                                    {
                                      Parsetree.ppat_desc =
                                        Parsetree.Ppat_any;
                                      Parsetree.ppat_loc = _loc;
                                      Parsetree.ppat_attributes = []
                                    };
                                  Parsetree.pvb_expr =
                                    {
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_apply
                                           ({
                                              Parsetree.pexp_desc =
                                                (Parsetree.Pexp_ident
                                                   {
                                                     Asttypes.txt =
                                                       (Longident.Lident
                                                          set_name);
                                                     Asttypes.loc = _loc
                                                   });
                                              Parsetree.pexp_loc = _loc;
                                              Parsetree.pexp_attributes = []
                                            }, [(Asttypes.Nolabel, r)]));
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    };
                                  Parsetree.pvb_attributes = [];
                                  Parsetree.pvb_loc = _loc
                                }]));
                        Parsetree.pstr_loc = _loc
                      }] @ str2))
              | (args,Some prio) ->
                  let r = coer (build_prio_alternatives _loc_r prio r)  in
                  let set_name = name ^ "__set__grammar"  in
                  (([{
                       Parsetree.pstr_desc =
                         (Parsetree.Pstr_value
                            (Asttypes.Nonrecursive,
                              [{
                                 Parsetree.pvb_pat =
                                   {
                                     Parsetree.ppat_desc =
                                       (Parsetree.Ppat_tuple
                                          [pname;
                                          {
                                            Parsetree.ppat_desc =
                                              (Parsetree.Ppat_var
                                                 {
                                                   Asttypes.txt = set_name;
                                                   Asttypes.loc = _loc
                                                 });
                                            Parsetree.ppat_loc = _loc;
                                            Parsetree.ppat_attributes = []
                                          }]);
                                     Parsetree.ppat_loc = _loc;
                                     Parsetree.ppat_attributes = []
                                   };
                                 Parsetree.pvb_expr =
                                   {
                                     Parsetree.pexp_desc =
                                       (Parsetree.Pexp_apply
                                          ({
                                             Parsetree.pexp_desc =
                                               (Parsetree.Pexp_ident
                                                  {
                                                    Asttypes.txt =
                                                      (Longident.Ldot
                                                         ((Longident.Lident
                                                             "Earley"),
                                                           "grammar_prio_family"));
                                                    Asttypes.loc = _loc
                                                  });
                                             Parsetree.pexp_loc = _loc;
                                             Parsetree.pexp_attributes = []
                                           },
                                            [(Asttypes.Nolabel,
                                               (Pa_ast.exp_string _loc name))]));
                                     Parsetree.pexp_loc = _loc;
                                     Parsetree.pexp_attributes = []
                                   };
                                 Parsetree.pvb_attributes = [];
                                 Parsetree.pvb_loc = _loc
                               }]));
                       Parsetree.pstr_loc = _loc
                     }] @ str1),
                    ([{
                        Parsetree.pstr_desc =
                          (Parsetree.Pstr_value
                             (Asttypes.Nonrecursive,
                               [{
                                  Parsetree.pvb_pat =
                                    {
                                      Parsetree.ppat_desc =
                                        Parsetree.Ppat_any;
                                      Parsetree.ppat_loc = _loc;
                                      Parsetree.ppat_attributes = []
                                    };
                                  Parsetree.pvb_expr =
                                    {
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_apply
                                           ({
                                              Parsetree.pexp_desc =
                                                (Parsetree.Pexp_ident
                                                   {
                                                     Asttypes.txt =
                                                       (Longident.Lident
                                                          set_name);
                                                     Asttypes.loc = _loc
                                                   });
                                              Parsetree.pexp_loc = _loc;
                                              Parsetree.pexp_attributes = []
                                            },
                                             [(Asttypes.Nolabel,
                                                {
                                                  Parsetree.pexp_desc =
                                                    (Parsetree.Pexp_fun
                                                       (Asttypes.Nolabel,
                                                         None, args_pat, r));
                                                  Parsetree.pexp_loc = _loc;
                                                  Parsetree.pexp_attributes =
                                                    []
                                                })]));
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    };
                                  Parsetree.pvb_attributes = [];
                                  Parsetree.pvb_loc = _loc
                                }]));
                        Parsetree.pstr_loc = _loc
                      }] @ str2))
               in
            let str2 =
              match (args, prio) with
              | ([],_)|(_::[],None ) -> str2
              | _ ->
                  let rec currify acc n =
                    function
                    | [] ->
                        (match prio with
                         | None  ->
                             {
                               Parsetree.pexp_desc =
                                 (Parsetree.Pexp_apply
                                    ({
                                       Parsetree.pexp_desc =
                                         (Parsetree.Pexp_ident
                                            {
                                              Asttypes.txt =
                                                (Longident.Lident name);
                                              Asttypes.loc = _loc
                                            });
                                       Parsetree.pexp_loc = _loc;
                                       Parsetree.pexp_attributes = []
                                     },
                                      [(Asttypes.Nolabel,
                                         (Pa_ast.exp_tuple _loc
                                            (List.rev acc)))]));
                               Parsetree.pexp_loc = _loc;
                               Parsetree.pexp_attributes = []
                             }
                         | Some _ ->
                             {
                               Parsetree.pexp_desc =
                                 (Parsetree.Pexp_fun
                                    (Asttypes.Nolabel, None,
                                      {
                                        Parsetree.ppat_desc =
                                          (Parsetree.Ppat_var
                                             {
                                               Asttypes.txt = "__curry__prio";
                                               Asttypes.loc = _loc
                                             });
                                        Parsetree.ppat_loc = _loc;
                                        Parsetree.ppat_attributes = []
                                      },
                                      {
                                        Parsetree.pexp_desc =
                                          (Parsetree.Pexp_apply
                                             ({
                                                Parsetree.pexp_desc =
                                                  (Parsetree.Pexp_ident
                                                     {
                                                       Asttypes.txt =
                                                         (Longident.Lident
                                                            name);
                                                       Asttypes.loc = _loc
                                                     });
                                                Parsetree.pexp_loc = _loc;
                                                Parsetree.pexp_attributes =
                                                  []
                                              },
                                               [(Asttypes.Nolabel,
                                                  (Pa_ast.exp_tuple _loc
                                                     (List.rev acc)));
                                               (Asttypes.Nolabel,
                                                 {
                                                   Parsetree.pexp_desc =
                                                     (Parsetree.Pexp_ident
                                                        {
                                                          Asttypes.txt =
                                                            (Longident.Lident
                                                               "__curry__prio");
                                                          Asttypes.loc = _loc
                                                        });
                                                   Parsetree.pexp_loc = _loc;
                                                   Parsetree.pexp_attributes
                                                     = []
                                                 })]));
                                        Parsetree.pexp_loc = _loc;
                                        Parsetree.pexp_attributes = []
                                      }));
                               Parsetree.pexp_loc = _loc;
                               Parsetree.pexp_attributes = []
                             })
                    | a::l ->
                        let v = "__curry__varx" ^ (string_of_int n)  in
                        let acc =
                          {
                            Parsetree.pexp_desc =
                              (Parsetree.Pexp_ident
                                 {
                                   Asttypes.txt = (Longident.Lident v);
                                   Asttypes.loc = _loc
                                 });
                            Parsetree.pexp_loc = _loc;
                            Parsetree.pexp_attributes = []
                          } :: acc  in
                        {
                          Parsetree.pexp_desc =
                            (Parsetree.Pexp_fun
                               (Asttypes.Nolabel, None,
                                 {
                                   Parsetree.ppat_desc =
                                     (Parsetree.Ppat_var
                                        {
                                          Asttypes.txt = v;
                                          Asttypes.loc = _loc
                                        });
                                   Parsetree.ppat_loc = _loc;
                                   Parsetree.ppat_attributes = []
                                 }, (currify acc (n + 1) l)));
                          Parsetree.pexp_loc = _loc;
                          Parsetree.pexp_attributes = []
                        }
                     in
                  let f = currify [] 0 args  in
                  [{
                     Parsetree.pstr_desc =
                       (Parsetree.Pstr_value
                          (Asttypes.Nonrecursive,
                            [{
                               Parsetree.pvb_pat = pname;
                               Parsetree.pvb_expr = f;
                               Parsetree.pvb_attributes = [];
                               Parsetree.pvb_loc = _loc
                             }]));
                     Parsetree.pstr_loc = _loc
                   }] @ str2
               in
            (str1, str2, str3)
         in
      let (str1,str2,str3) = fn l  in
      if str3 = []
      then str1 @ str2
      else
        str1 @
          ([{
              Parsetree.pstr_desc =
                (Parsetree.Pstr_value (Asttypes.Recursive, str3));
              Parsetree.pstr_loc = _loc
            }] @ str2)
      
    let glr_sequence = Earley.declare_grammar "glr_sequence" 
    let glr_opt_expr = Earley.declare_grammar "glr_opt_expr" 
    let glr_option = Earley.declare_grammar "glr_option" 
    let glr_ident = Earley.declare_grammar "glr_ident" 
    let glr_left_member = Earley.declare_grammar "glr_left_member" 
    let glr_let = Earley.declare_grammar "glr_let" 
    let glr_cond = Earley.declare_grammar "glr_cond" 
    let (glr_action,glr_action__set__grammar) =
      Earley.grammar_family "glr_action" 
    let (glr_rule,glr_rule__set__grammar) = Earley.grammar_family "glr_rule" 
    let (glr_at_rule,glr_at_rule__set__grammar) =
      Earley.grammar_family "glr_at_rule" 
    let glr_rules = Earley.declare_grammar "glr_rules" 
    let _ =
      Earley.set_grammar glr_sequence
        (Earley.alternatives
           [Earley.fsequence (Earley.string "(" "(")
              (Earley.sequence expression (Earley.string ")" ")")
                 (fun e  -> fun _  -> fun _  -> (true, e)));
           Earley.fsequence (Earley.char '{' '{')
             (Earley.sequence
                (Earley.apply_position
                   (fun x  ->
                      fun str  ->
                        fun pos  ->
                          fun str'  ->
                            fun pos'  -> ((locate str pos str' pos'), x))
                   glr_rules) (Earley.char '}' '}')
                (fun r  ->
                   let (_loc_r,r) = r  in
                   fun _  -> fun _  -> (true, (build_alternatives _loc_r r))));
           Earley.sequence_position (Earley.string "EOF" "EOF") glr_opt_expr
             (fun _  ->
                fun oe  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          ((oe <> None),
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "eof"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    },
                                     [(Asttypes.Nolabel,
                                        (from_opt oe
                                           {
                                             Parsetree.pexp_desc =
                                               (Parsetree.Pexp_construct
                                                  ({
                                                     Asttypes.txt =
                                                       (Longident.Lident "()");
                                                     Asttypes.loc = _loc
                                                   }, None));
                                             Parsetree.pexp_loc = _loc;
                                             Parsetree.pexp_attributes = []
                                           }))]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.sequence_position (Earley.string "EMPTY" "EMPTY")
             glr_opt_expr
             (fun _  ->
                fun oe  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          ((oe <> None),
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "empty"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    },
                                     [(Asttypes.Nolabel,
                                        (from_opt oe
                                           {
                                             Parsetree.pexp_desc =
                                               (Parsetree.Pexp_construct
                                                  ({
                                                     Asttypes.txt =
                                                       (Longident.Lident "()");
                                                     Asttypes.loc = _loc
                                                   }, None));
                                             Parsetree.pexp_loc = _loc;
                                             Parsetree.pexp_attributes = []
                                           }))]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.sequence_position (Earley.string "FAIL" "FAIL") expr_arg
             (fun _  ->
                fun e  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          (false,
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "fail"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    }, [(Asttypes.Nolabel, e)]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.sequence_position (Earley.string "DEBUG" "DEBUG") expr_arg
             (fun _  ->
                fun e  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          (false,
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "debug"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    }, [(Asttypes.Nolabel, e)]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.apply_position
             (fun _  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos
                           in
                        (true,
                          {
                            Parsetree.pexp_desc =
                              (Parsetree.Pexp_ident
                                 {
                                   Asttypes.txt =
                                     (Longident.Ldot
                                        ((Longident.Lident "Earley"), "any"));
                                   Asttypes.loc = _loc
                                 });
                            Parsetree.pexp_loc = _loc;
                            Parsetree.pexp_attributes = []
                          })) (Earley.string "ANY" "ANY");
           Earley.fsequence_position (Earley.string "CHR" "CHR")
             (Earley.sequence expr_arg glr_opt_expr
                (fun e  ->
                   fun oe  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               ((oe <> None),
                                 {
                                   Parsetree.pexp_desc =
                                     (Parsetree.Pexp_apply
                                        ({
                                           Parsetree.pexp_desc =
                                             (Parsetree.Pexp_ident
                                                {
                                                  Asttypes.txt =
                                                    (Longident.Ldot
                                                       ((Longident.Lident
                                                           "Earley"), "char"));
                                                  Asttypes.loc = _loc
                                                });
                                           Parsetree.pexp_loc = _loc;
                                           Parsetree.pexp_attributes = []
                                         },
                                          [(Asttypes.Nolabel, e);
                                          (Asttypes.Nolabel, (from_opt oe e))]));
                                   Parsetree.pexp_loc = _loc;
                                   Parsetree.pexp_attributes = []
                                 })));
           Earley.sequence_position char_litteral glr_opt_expr
             (fun c  ->
                fun oe  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          let e = Pa_ast.exp_char _loc c  in
                          ((oe <> None),
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "char"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    },
                                     [(Asttypes.Nolabel, e);
                                     (Asttypes.Nolabel, (from_opt oe e))]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.fsequence_position (Earley.string "STR" "STR")
             (Earley.sequence expr_arg glr_opt_expr
                (fun e  ->
                   fun oe  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               ((oe <> None),
                                 {
                                   Parsetree.pexp_desc =
                                     (Parsetree.Pexp_apply
                                        ({
                                           Parsetree.pexp_desc =
                                             (Parsetree.Pexp_ident
                                                {
                                                  Asttypes.txt =
                                                    (Longident.Ldot
                                                       ((Longident.Lident
                                                           "Earley"),
                                                         "string"));
                                                  Asttypes.loc = _loc
                                                });
                                           Parsetree.pexp_loc = _loc;
                                           Parsetree.pexp_attributes = []
                                         },
                                          [(Asttypes.Nolabel, e);
                                          (Asttypes.Nolabel, (from_opt oe e))]));
                                   Parsetree.pexp_loc = _loc;
                                   Parsetree.pexp_attributes = []
                                 })));
           Earley.sequence_position (Earley.string "ERROR" "ERROR") expr_arg
             (fun _  ->
                fun e  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          (true,
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "error_message"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    },
                                     [(Asttypes.Nolabel,
                                        {
                                          Parsetree.pexp_desc =
                                            (Parsetree.Pexp_fun
                                               (Asttypes.Nolabel, None,
                                                 {
                                                   Parsetree.ppat_desc =
                                                     (Parsetree.Ppat_construct
                                                        ({
                                                           Asttypes.txt =
                                                             (Longident.Lident
                                                                "()");
                                                           Asttypes.loc =
                                                             _loc
                                                         }, None));
                                                   Parsetree.ppat_loc = _loc;
                                                   Parsetree.ppat_attributes
                                                     = []
                                                 }, e));
                                          Parsetree.pexp_loc = _loc;
                                          Parsetree.pexp_attributes = []
                                        })]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.sequence_position string_litteral glr_opt_expr
             (fun s  ->
                fun oe  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          if (String.length s) = 0 then Earley.give_up ();
                          (let s = Pa_ast.exp_string _loc s  in
                           let e = from_opt oe s  in
                           ((oe <> None),
                             {
                               Parsetree.pexp_desc =
                                 (Parsetree.Pexp_apply
                                    ({
                                       Parsetree.pexp_desc =
                                         (Parsetree.Pexp_ident
                                            {
                                              Asttypes.txt =
                                                (Longident.Ldot
                                                   ((Longident.Lident
                                                       "Earley"), "string"));
                                              Asttypes.loc = _loc
                                            });
                                       Parsetree.pexp_loc = _loc;
                                       Parsetree.pexp_attributes = []
                                     },
                                      [(Asttypes.Nolabel, s);
                                      (Asttypes.Nolabel, e)]));
                               Parsetree.pexp_loc = _loc;
                               Parsetree.pexp_attributes = []
                             })));
           Earley.fsequence_position (Earley.string "RE" "RE")
             (Earley.sequence expr_arg glr_opt_expr
                (fun e  ->
                   fun opt  ->
                     fun _  ->
                       fun __loc__start__buf  ->
                         fun __loc__start__pos  ->
                           fun __loc__end__buf  ->
                             fun __loc__end__pos  ->
                               let _loc =
                                 locate __loc__start__buf __loc__start__pos
                                   __loc__end__buf __loc__end__pos
                                  in
                               let act =
                                 {
                                   Parsetree.pexp_desc =
                                     (Parsetree.Pexp_fun
                                        (Asttypes.Nolabel, None,
                                          {
                                            Parsetree.ppat_desc =
                                              (Parsetree.Ppat_var
                                                 {
                                                   Asttypes.txt = "groupe";
                                                   Asttypes.loc = _loc
                                                 });
                                            Parsetree.ppat_loc = _loc;
                                            Parsetree.ppat_attributes = []
                                          },
                                          (from_opt opt
                                             {
                                               Parsetree.pexp_desc =
                                                 (Parsetree.Pexp_apply
                                                    ({
                                                       Parsetree.pexp_desc =
                                                         (Parsetree.Pexp_ident
                                                            {
                                                              Asttypes.txt =
                                                                (Longident.Lident
                                                                   "groupe");
                                                              Asttypes.loc =
                                                                _loc
                                                            });
                                                       Parsetree.pexp_loc =
                                                         _loc;
                                                       Parsetree.pexp_attributes
                                                         = []
                                                     },
                                                      [(Asttypes.Nolabel,
                                                         {
                                                           Parsetree.pexp_desc
                                                             =
                                                             (Parsetree.Pexp_constant
                                                                (Parsetree.Pconst_integer
                                                                   ("0",
                                                                    None)));
                                                           Parsetree.pexp_loc
                                                             = _loc;
                                                           Parsetree.pexp_attributes
                                                             = []
                                                         })]));
                                               Parsetree.pexp_loc = _loc;
                                               Parsetree.pexp_attributes = []
                                             })));
                                   Parsetree.pexp_loc = _loc;
                                   Parsetree.pexp_attributes = []
                                 }  in
                               match e.pexp_desc with
                               | Pexp_ident { txt = Lident id } ->
                                   let id =
                                     let l = String.length id  in
                                     if
                                       (l > 3) &&
                                         ((String.sub id (l - 3) 3) = "_re")
                                     then String.sub id 0 (l - 3)
                                     else id  in
                                   (true,
                                     {
                                       Parsetree.pexp_desc =
                                         (Parsetree.Pexp_apply
                                            ({
                                               Parsetree.pexp_desc =
                                                 (Parsetree.Pexp_ident
                                                    {
                                                      Asttypes.txt =
                                                        (Longident.Ldot
                                                           ((Longident.Lident
                                                               "EarleyStr"),
                                                             "regexp"));
                                                      Asttypes.loc = _loc
                                                    });
                                               Parsetree.pexp_loc = _loc;
                                               Parsetree.pexp_attributes = []
                                             },
                                              [((Asttypes.Labelled "name"),
                                                 (Pa_ast.exp_string _loc id));
                                              (Asttypes.Nolabel, e);
                                              (Asttypes.Nolabel, act)]));
                                       Parsetree.pexp_loc = _loc;
                                       Parsetree.pexp_attributes = []
                                     })
                               | _ ->
                                   (true,
                                     {
                                       Parsetree.pexp_desc =
                                         (Parsetree.Pexp_apply
                                            ({
                                               Parsetree.pexp_desc =
                                                 (Parsetree.Pexp_ident
                                                    {
                                                      Asttypes.txt =
                                                        (Longident.Ldot
                                                           ((Longident.Lident
                                                               "EarleyStr"),
                                                             "regexp"));
                                                      Asttypes.loc = _loc
                                                    });
                                               Parsetree.pexp_loc = _loc;
                                               Parsetree.pexp_attributes = []
                                             },
                                              [(Asttypes.Nolabel, e);
                                              (Asttypes.Nolabel, act)]));
                                       Parsetree.pexp_loc = _loc;
                                       Parsetree.pexp_attributes = []
                                     })));
           Earley.sequence_position (Earley.string "BLANK" "BLANK")
             glr_opt_expr
             (fun _  ->
                fun oe  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          let e =
                            from_opt oe
                              {
                                Parsetree.pexp_desc =
                                  (Parsetree.Pexp_construct
                                     ({
                                        Asttypes.txt =
                                          (Longident.Lident "()");
                                        Asttypes.loc = _loc
                                      }, None));
                                Parsetree.pexp_loc = _loc;
                                Parsetree.pexp_attributes = []
                              }
                             in
                          ((oe <> None),
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "with_blank_test"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    }, [(Asttypes.Nolabel, e)]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.sequence_position dash glr_opt_expr
             (fun _default_0  ->
                fun oe  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          let e =
                            from_opt oe
                              {
                                Parsetree.pexp_desc =
                                  (Parsetree.Pexp_construct
                                     ({
                                        Asttypes.txt =
                                          (Longident.Lident "()");
                                        Asttypes.loc = _loc
                                      }, None));
                                Parsetree.pexp_loc = _loc;
                                Parsetree.pexp_attributes = []
                              }
                             in
                          ((oe <> None),
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "no_blank_test"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    }, [(Asttypes.Nolabel, e)]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.sequence_position regexp_litteral glr_opt_expr
             (fun s  ->
                fun oe  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          let opt =
                            from_opt oe
                              {
                                Parsetree.pexp_desc =
                                  (Parsetree.Pexp_apply
                                     ({
                                        Parsetree.pexp_desc =
                                          (Parsetree.Pexp_ident
                                             {
                                               Asttypes.txt =
                                                 (Longident.Lident "groupe");
                                               Asttypes.loc = _loc
                                             });
                                        Parsetree.pexp_loc = _loc;
                                        Parsetree.pexp_attributes = []
                                      },
                                       [(Asttypes.Nolabel,
                                          {
                                            Parsetree.pexp_desc =
                                              (Parsetree.Pexp_constant
                                                 (Parsetree.Pconst_integer
                                                    ("0", None)));
                                            Parsetree.pexp_loc = _loc;
                                            Parsetree.pexp_attributes = []
                                          })]));
                                Parsetree.pexp_loc = _loc;
                                Parsetree.pexp_attributes = []
                              }
                             in
                          let es = String.escaped s  in
                          let act =
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_fun
                                   (Asttypes.Nolabel, None,
                                     {
                                       Parsetree.ppat_desc =
                                         (Parsetree.Ppat_var
                                            {
                                              Asttypes.txt = "groupe";
                                              Asttypes.loc = _loc
                                            });
                                       Parsetree.ppat_loc = _loc;
                                       Parsetree.ppat_attributes = []
                                     }, opt));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }  in
                          (true,
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident
                                                      "EarleyStr"), "regexp"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    },
                                     [((Asttypes.Labelled "name"),
                                        (Pa_ast.exp_string _loc es));
                                     (Asttypes.Nolabel,
                                       (Pa_ast.exp_string _loc s));
                                     (Asttypes.Nolabel, act)]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }));
           Earley.sequence_position new_regexp_litteral glr_opt_expr
             (fun s  ->
                fun opt  ->
                  fun __loc__start__buf  ->
                    fun __loc__start__pos  ->
                      fun __loc__end__buf  ->
                        fun __loc__end__pos  ->
                          let _loc =
                            locate __loc__start__buf __loc__start__pos
                              __loc__end__buf __loc__end__pos
                             in
                          let es = String.escaped s  in
                          let s = "\\(" ^ (s ^ "\\)")  in
                          let re =
                            {
                              Parsetree.pexp_desc =
                                (Parsetree.Pexp_apply
                                   ({
                                      Parsetree.pexp_desc =
                                        (Parsetree.Pexp_ident
                                           {
                                             Asttypes.txt =
                                               (Longident.Ldot
                                                  ((Longident.Lident "Earley"),
                                                    "regexp"));
                                             Asttypes.loc = _loc
                                           });
                                      Parsetree.pexp_loc = _loc;
                                      Parsetree.pexp_attributes = []
                                    },
                                     [((Asttypes.Labelled "name"),
                                        (Pa_ast.exp_string _loc es));
                                     (Asttypes.Nolabel,
                                       (Pa_ast.exp_string _loc s))]));
                              Parsetree.pexp_loc = _loc;
                              Parsetree.pexp_attributes = []
                            }  in
                          match opt with
                          | None  -> (true, re)
                          | Some e ->
                              (true,
                                {
                                  Parsetree.pexp_desc =
                                    (Parsetree.Pexp_apply
                                       ({
                                          Parsetree.pexp_desc =
                                            (Parsetree.Pexp_ident
                                               {
                                                 Asttypes.txt =
                                                   (Longident.Ldot
                                                      ((Longident.Lident
                                                          "Earley"), "apply"));
                                                 Asttypes.loc = _loc
                                               });
                                          Parsetree.pexp_loc = _loc;
                                          Parsetree.pexp_attributes = []
                                        },
                                         [(Asttypes.Nolabel,
                                            {
                                              Parsetree.pexp_desc =
                                                (Parsetree.Pexp_fun
                                                   (Asttypes.Nolabel, None,
                                                     {
                                                       Parsetree.ppat_desc =
                                                         (Parsetree.Ppat_var
                                                            {
                                                              Asttypes.txt =
                                                                "group";
                                                              Asttypes.loc =
                                                                _loc
                                                            });
                                                       Parsetree.ppat_loc =
                                                         _loc;
                                                       Parsetree.ppat_attributes
                                                         = []
                                                     }, e));
                                              Parsetree.pexp_loc = _loc;
                                              Parsetree.pexp_attributes = []
                                            });
                                         (Asttypes.Nolabel, re)]));
                                  Parsetree.pexp_loc = _loc;
                                  Parsetree.pexp_attributes = []
                                }));
           Earley.apply_position
             (fun id  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos
                           in
                        (true,
                          {
                            Parsetree.pexp_desc =
                              (Parsetree.Pexp_ident
                                 { Asttypes.txt = id; Asttypes.loc = _loc });
                            Parsetree.pexp_loc = _loc;
                            Parsetree.pexp_attributes = []
                          })) value_path])
      
    let _ =
      Earley.set_grammar glr_opt_expr
        (Earley.option None
           (Earley.apply (fun x  -> Some x)
              (Earley.fsequence (Earley.char '[' '[')
                 (Earley.sequence expression (Earley.char ']' ']')
                    (fun _default_0  -> fun _  -> fun _  -> _default_0)))))
      
    let _ =
      Earley.set_grammar glr_option
        (Earley.alternatives
           [Earley.apply (fun _  -> `Once) (Earley.empty ());
           Earley.fsequence (Earley.char '*' '*')
             (Earley.sequence glr_opt_expr
                (Earley.option None
                   (Earley.apply (fun x  -> Some x) (Earley.char '$' '$')))
                (fun e  -> fun g  -> fun _  -> `Fixpoint (e, g)));
           Earley.fsequence (Earley.char '+' '+')
             (Earley.sequence glr_opt_expr
                (Earley.option None
                   (Earley.apply (fun x  -> Some x) (Earley.char '$' '$')))
                (fun e  -> fun g  -> fun _  -> `Fixpoint1 (e, g)));
           Earley.fsequence (Earley.char '?' '?')
             (Earley.sequence glr_opt_expr
                (Earley.option None
                   (Earley.apply (fun x  -> Some x) (Earley.char '$' '$')))
                (fun e  -> fun g  -> fun _  -> `Option (e, g)));
           Earley.apply (fun _  -> `Greedy) (Earley.char '$' '$')])
      
    let _ =
      Earley.set_grammar glr_ident
        (Earley.alternatives
           [Earley.apply (fun _  -> (None, ("_", None))) (Earley.empty ());
           Earley.sequence (pattern_lvl (true, ConstrPat))
             (Earley.char ':' ':')
             (fun p  ->
                fun _  ->
                  match p.ppat_desc with
                  | Ppat_alias (p,{ txt = id }) ->
                      ((Some true), (id, (Some p)))
                  | Ppat_var { txt = id } -> ((Some (id <> "_")), (id, None))
                  | Ppat_any  -> ((Some false), ("_", None))
                  | _ -> ((Some true), ("_", (Some p))))])
      
    let _ =
      Earley.set_grammar glr_left_member
        (Earley.apply List.rev
           (Earley.fixpoint1 []
              (Earley.apply (fun x  -> fun y  -> x :: y)
                 (Earley.fsequence glr_ident
                    (Earley.sequence glr_sequence glr_option
                       (fun ((cst,s) as _default_0)  ->
                          fun opt  ->
                            fun ((cst',id) as _default_1)  ->
                              `Normal
                                (id, (from_opt cst' ((opt <> `Once) || cst)),
                                  s, opt)))))))
      
    let _ =
      Earley.set_grammar glr_let
        (Earley.alternatives
           [Earley.apply (fun _  -> fun x  -> x) (Earley.empty ());
           Earley.fsequence_position let_kw
             (Earley.fsequence rec_flag
                (Earley.fsequence let_binding
                   (Earley.sequence in_kw glr_let
                      (fun _default_0  ->
                         fun l  ->
                           fun lbs  ->
                             fun r  ->
                               fun _default_1  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos
                                            in
                                         fun x  ->
                                           Exp.let_ ~loc:_loc r lbs (l x)))))])
      
    let _ =
      Earley.set_grammar glr_cond
        (Earley.option None
           (Earley.apply (fun x  -> Some x)
              (Earley.sequence when_kw expression (fun _  -> fun e  -> e))))
      
    let _ =
      glr_action__set__grammar
        (fun alm  ->
           Earley.alternatives
             [Earley.apply (fun _  -> Default) (Earley.empty ());
             Earley.sequence (Earley.string "->>" "->>") (glr_rule alm)
               (fun _  ->
                  fun r  -> let (a,b,c) = build_rule r  in DepSeq (a, b, c));
             Earley.fsequence arrow_re
               (Earley.sequence
                  (if alm then expression else expression_lvl (Let, Seq))
                  no_semi
                  (fun action  ->
                     fun _default_0  -> fun _default_1  -> Normal action))])
      
    let _ =
      glr_rule__set__grammar
        (fun alm  ->
           Earley.fsequence_position glr_let
             (Earley.fsequence glr_left_member
                (Earley.sequence glr_cond (glr_action alm)
                   (fun condition  ->
                      fun action  ->
                        fun l  ->
                          fun def  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos
                                       in
                                    let l =
                                      fst
                                        (List.fold_right
                                           (fun x  ->
                                              fun (res,i)  ->
                                                match x with
                                                | `Normal (("_",a),true ,c,d)
                                                    ->
                                                    (((`Normal
                                                         ((("_default_" ^
                                                              (string_of_int
                                                                 i)), a),
                                                           true, c, d, false))
                                                      :: res), (i + 1))
                                                | `Normal (id,b,c,d) ->
                                                    let occur_loc_id =
                                                      ((fst id) <> "_") &&
                                                        (occur
                                                           ("_loc_" ^
                                                              (fst id))
                                                           action)
                                                       in
                                                    (((`Normal
                                                         (id, b, c, d,
                                                           occur_loc_id)) ::
                                                      res), i)) l ([], 0))
                                       in
                                    let occur_loc = occur "_loc" action  in
                                    (_loc, occur_loc, def, l, condition,
                                      action)))))
      
    let _ =
      glr_at_rule__set__grammar
        (fun alm  ->
           Earley.sequence
             (Earley.option None
                (Earley.apply (fun x  -> Some x)
                   (Earley.alternatives
                      [Earley.fsequence (Earley.char '[' '[')
                         (Earley.fsequence (Earley.char '@' '@')
                            (Earley.sequence
                               (Earley.string "unshared" "unshared")
                               (Earley.char ']' ']')
                               (fun _  -> fun _  -> fun _  -> fun _  -> ())));
                      Earley.apply (fun _  -> ()) (Earley.char '@' '@')])))
             (glr_rule alm) (fun a  -> fun r  -> ((a <> None), r)))
      
    let _ =
      Earley.set_grammar glr_rules
        (Earley.fsequence
           (Earley.option None
              (Earley.apply (fun x  -> Some x) (Earley.char '|' '|')))
           (Earley.sequence
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y)
                       (Earley.sequence (glr_at_rule false)
                          (Earley.char '|' '|') (fun r  -> fun _  -> r)))))
              (glr_at_rule true)
              (fun rs  -> fun r  -> fun _default_0  -> r :: rs)))
      
    let glr_binding = Earley.declare_grammar "glr_binding" 
    let _ =
      Earley.set_grammar glr_binding
        (Earley.fsequence lident
           (Earley.fsequence
              (Earley.apply List.rev
                 (Earley.fixpoint []
                    (Earley.apply (fun x  -> fun y  -> x :: y) pattern)))
              (Earley.fsequence
                 (Earley.option None
                    (Earley.apply (fun x  -> Some x)
                       (Earley.sequence (Earley.char '@' '@') pattern
                          (fun _  -> fun _default_0  -> _default_0))))
                 (Earley.fsequence
                    (Earley.option None
                       (Earley.apply (fun x  -> Some x)
                          (Earley.sequence (Earley.char ':' ':') typexpr
                             (fun _  -> fun _default_0  -> _default_0))))
                    (Earley.sequence (Earley.char '=' '=')
                       (Earley.apply_position
                          (fun x  ->
                             fun str  ->
                               fun pos  ->
                                 fun str'  ->
                                   fun pos'  ->
                                     ((locate str pos str' pos'), x))
                          glr_rules)
                       (fun _  ->
                          fun r  ->
                            let (_loc_r,r) = r  in
                            fun ty  ->
                              fun prio  ->
                                fun args  ->
                                  fun name  ->
                                    `Parser (name, args, prio, ty, _loc_r, r)))))))
      
    let glr_bindings = Earley.declare_grammar "glr_bindings" 
    let _ =
      Earley.set_grammar glr_bindings
        (Earley.alternatives
           [Earley.fsequence and_kw
              (Earley.fsequence
                 (Earley.option []
                    (Earley.sequence let_binding and_kw
                       (fun _default_0  -> fun _  -> _default_0)))
                 (Earley.fsequence parser_kw
                    (Earley.sequence glr_binding glr_bindings
                       (fun b  ->
                          fun l  ->
                            fun _default_0  ->
                              fun cs  ->
                                fun _default_1  ->
                                  (List.map (fun b  -> `Caml b) cs) @ (b ::
                                    l)))));
           Earley.apply (fun cs  -> List.map (fun b  -> `Caml b) cs)
             (Earley.option []
                (Earley.sequence and_kw let_binding
                   (fun _  -> fun _default_0  -> _default_0)))])
      
    let extra_structure =
      let p =
        Earley.fsequence_position let_kw
          (Earley.fsequence parser_kw
             (Earley.sequence glr_binding glr_bindings
                (fun b  ->
                   fun l  ->
                     fun _default_0  ->
                       fun _default_1  ->
                         fun __loc__start__buf  ->
                           fun __loc__start__pos  ->
                             fun __loc__end__buf  ->
                               fun __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos
                                    in
                                 build_str_item _loc (b :: l))))
         in
      p :: extra_structure 
    let extra_prefix_expressions =
      let p =
        Earley.sequence_position
          (Earley.alternatives
             [Earley.fsequence function_kw
                (Earley.fsequence pattern
                   (Earley.fsequence (Earley.char '@' '@')
                      (Earley.fsequence pattern
                         (Earley.sequence arrow_re parser_kw
                            (fun _  ->
                               fun _  ->
                                 fun prio  ->
                                   fun _  ->
                                     fun arg  ->
                                       fun _  -> ([arg], (Some prio)))))));
             Earley.apply (fun _  -> ([], None)) parser_kw;
             Earley.fsequence fun_kw
               (Earley.fsequence
                  (Earley.apply List.rev
                     (Earley.fixpoint []
                        (Earley.apply (fun x  -> fun y  -> x :: y)
                           (pattern_lvl (false, AtomPat)))))
                  (Earley.fsequence (Earley.char '@' '@')
                     (Earley.fsequence pattern
                        (Earley.sequence arrow_re parser_kw
                           (fun _  ->
                              fun _  ->
                                fun prio  ->
                                  fun _  ->
                                    fun args  ->
                                      fun _  -> (args, (Some prio)))))))])
          (Earley.apply_position
             (fun x  ->
                fun str  ->
                  fun pos  ->
                    fun str'  -> fun pos'  -> ((locate str pos str' pos'), x))
             glr_rules)
          (fun ((args,prio) as _default_0)  ->
             fun r  ->
               let (_loc_r,r) = r  in
               fun __loc__start__buf  ->
                 fun __loc__start__pos  ->
                   fun __loc__end__buf  ->
                     fun __loc__end__pos  ->
                       let _loc =
                         locate __loc__start__buf __loc__start__pos
                           __loc__end__buf __loc__end__pos
                          in
                       let r =
                         match prio with
                         | None  -> build_alternatives _loc_r r
                         | Some prio -> build_prio_alternatives _loc_r prio r
                          in
                       List.fold_right
                         (fun arg  ->
                            fun r  ->
                              {
                                Parsetree.pexp_desc =
                                  (Parsetree.Pexp_fun
                                     (Asttypes.Nolabel, None, arg, r));
                                Parsetree.pexp_loc = _loc;
                                Parsetree.pexp_attributes = []
                              }) args r)
         in
      p :: extra_prefix_expressions 
    let _ = add_reserved_id "parser" 
  end
