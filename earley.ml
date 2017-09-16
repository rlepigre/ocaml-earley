(*
  ======================================================================
  Copyright Christophe Raffalli & Rodolphe Lepigre
  LAMA, UMR 5127 CNRS, Université Savoie Mont Blanc

  christophe.raffalli@univ-savoie.fr
  rodolphe.lepigre@univ-savoie.fr

  This software contains a parser combinator library for the OCaml lang-
  uage. It is intended to be used in conjunction with pa_ocaml (an OCaml
  parser and syntax extention mechanism) to provide  a  fully-integrated
  way of building parsers using an extention of OCaml's syntax.

  This software is governed by the CeCILL-B license under French law and
  abiding by the rules of distribution of free software.  You  can  use,
  modify and/or redistribute the software under the terms of the CeCILL-
  B license as circulated by CEA, CNRS and INRIA at the following URL.

      http://www.cecill.info

  As a counterpart to the access to the source code and  rights to copy,
  modify and redistribute granted by the  license,  users  are  provided
  only with a limited warranty  and the software's author, the holder of
  the economic rights, and the successive licensors  have  only  limited
  liability.

  In this respect, the user's attention is drawn to the risks associated
  with loading, using, modifying and/or developing  or  reproducing  the
  software by the user in light of its specific status of free software,
  that may mean that it is complicated  to  manipulate,  and  that  also
  therefore means that it is reserved  for  developers  and  experienced
  professionals having in-depth computer knowledge. Users are  therefore
  encouraged to load and test  the  software's  suitability  as  regards
  their requirements in conditions enabling the security of  their  sys-
  tems and/or data to be ensured and, more generally, to use and operate
  it in the same conditions as regards security.

  The fact that you are presently reading this means that you  have  had
  knowledge of the CeCILL-B license and that you accept its terms.
  ======================================================================
*)

open EarleyUtils
open Input
open EarleyEngine

type blank = EarleyEngine.blank
type 'a grammar = 'a EarleyEngine.grammar

exception Parse_error = EarleyEngine.Parse_error

let warn_merge = EarleyEngine.warn_merge

let debug_lvl = EarleyEngine.debug_lvl

let give_up () = raise Error

let no_blank str pos = str, pos

let partial_parse_buffer : type a.a grammar -> blank -> ?blank_after:bool -> buffer -> int -> a * buffer * int
   = fun g bl ?(blank_after=true) buf pos ->
       parse_buffer_aux (init_errpos buf pos) false blank_after g bl buf pos

let solo = fun ?(name=new_name ()) ?(accept_empty=false) set s ->
  let j = Fixpoint.from_val (accept_empty,set) in
  (j, [(Next(j,name,Term (set, s),Idt,idtEmpty),Container.create ())])

let greedy_solo =
  fun ?(name=new_name ()) i s ->
    let cache = Hashtbl.create 101 in
    let s = fun ptr blank b p b' p' ->
      let key = (buffer_uid b, p, buffer_uid b', p') in
      let l = try Hashtbl.find cache key with Not_found -> [] in
      try
        let (_,_,r) = List.find (fun (p, bl, _) -> p == ptr && bl == blank) l in
        r
      with Not_found ->
        let r = s ptr blank b p b' p' in
        let l = (ptr,blank,r)::l in
        Hashtbl.replace cache key l;
        r
    in
    (i, [(Next(i,name,Greedy(i,s),Idt,idtEmpty),Container.create ())])

let test = fun ?(name=new_name ()) set f ->
  let i = (true,set) in
  let j = Fixpoint.from_val i in
  (j, [(Next(j,name,Test (set, (fun _ _ -> f)),Idt,idtEmpty),Container.create ())])

let blank_test = fun ?(name=new_name ()) set f ->
  let i = (true,set) in
  let j = Fixpoint.from_val i in
  (j, [(Next(j,name,Test (set, f),Idt,idtEmpty),Container.create ())])

let success_test a = test ~name:"SUCCESS" Charset.full (fun _ _ -> (a, true))

let with_blank_test a = blank_test ~name:"BLANK" Charset.full
  (fun buf' pos' buf pos -> (a, not (buffer_equal buf' buf) || pos' <> pos))

let no_blank_test a = blank_test ~name:"NOBLANK" Charset.full
  (fun buf' pos' buf pos -> (a, buffer_equal buf' buf && pos' = pos))

let nonterm (i,s) = NonTerm(i,ref s)

let next_aux name s f r = (Next(compose_info s r, name, s,f,r), Container.create ())

let next : type a b c. a grammar -> (a -> b) pos -> (b -> c) rule -> c rule =
  fun s f r -> match snd s with
  | [(Next(i,name,s0,g,(Empty h,_)),_)] ->
     next_aux name s0 (compose3 f h g) r
  | _ -> next_aux (new_name ()) (nonterm s) f r

let eof : 'a -> 'a grammar
  = fun a ->
    let fn buf pos =
      if is_empty buf pos then (a,buf,pos) else raise Error
    in
    solo (Charset.singleton '\255') fn

let mk_grammar s = (grammar_info s, s)

let give_name name (i,_ as g) =
  (i, [grammar_to_rule ~name g])

let apply : type a b. (a -> b) -> a grammar -> b grammar = fun f l1 ->
  mk_grammar [next l1 (Simple f) idtEmpty]

let apply_position : type a b. (a -> buffer -> int -> buffer -> int -> b) -> a grammar -> b grammar = fun f l1 ->
  mk_grammar [next l1 Idt (Empty(WithPos(fun b p b' p' a -> f a b p b' p')),Container.create ())]

let sequence : 'a grammar -> 'b grammar -> ('a -> 'b -> 'c) -> 'c grammar
  = fun l1 l2 f -> mk_grammar [next l1 Idt (next l2 (Simple (fun b a -> f a b)) idtEmpty)]

let sequence_position : 'a grammar -> 'b grammar -> ('a -> 'b -> buffer -> int -> buffer -> int -> 'c) -> 'c grammar
   = fun l1 l2 f ->
    mk_grammar [next l1 Idt (next l2 Idt (Empty(WithPos(fun b p b' p' a' a -> f a a' b p b' p')),Container.create ()))]

let parse_buffer : 'a grammar -> blank -> buffer -> 'a =
  fun g blank buf ->
    let g = sequence g (eof ()) (fun x _ -> x) in
    let (a, _, _) = partial_parse_buffer g blank buf 0 in
    a

let parse_string ?(filename="") grammar blank str =
  let str = Input.from_string ~filename str in
  parse_buffer grammar blank str

let parse_channel ?(filename="") grammar blank ic  =
  let str = Input.from_channel ~filename ic in
  parse_buffer grammar blank str

let parse_file grammar blank filename  =
  let str = Input.from_file filename in
  parse_buffer grammar blank str

module WithPP(PP : Preprocessor) =
  struct
    module InPP = Input.WithPP(PP)

    let parse_string ?(filename="") grammar blank str =
      let str = InPP.from_string ~filename str in
      parse_buffer grammar blank str

    let parse_channel ?(filename="") grammar blank ic  =
      let str = InPP.from_channel ~filename ic in
      parse_buffer grammar blank str

    let parse_file grammar blank filename  =
      let str = InPP.from_file filename in
      parse_buffer grammar blank str
  end

let fail : unit -> 'a grammar
  = fun () ->
    let fn buf pos = raise Error in
    solo Charset.empty fn

let error_message : (unit -> string) -> 'a grammar
  = fun msg ->
    (* compose with a test with a full charset to pass the final charset test in
       internal_parse_buffer *)
    let i = (false,Charset.full) in
    let j = Fixpoint.from_val i in
    let fn errpos blank _ _ buf pos =
      add_errmsg errpos buf pos msg;
      raise Error
    in
    (j, [(Next(j,"error",Greedy (j, fn),Idt,idtEmpty),Container.create ())])

let unset : string -> 'a grammar
  = fun msg ->
    let fn buf pos =
      failwith msg
    in
    solo Charset.empty fn (* make sure we have the message *)

let declare_grammar name =
  let g = snd (unset (name ^ " not set")) in
  let ptr = ref g in
  let j = Fixpoint.from_ref ptr grammar_info in
  mk_grammar [(Next(j,name,NonTerm (j, ptr),Idt, idtEmpty),Container.create ())]

let set_grammar : type a.a grammar -> a grammar -> unit = fun p1 p2 ->
  match snd p1 with
  | [(Next(_,name,NonTerm(i,ptr),f,e),_)] ->
     (match f === Idt, e === idtEmpty with
     | Eq, Eq -> ptr := snd p2; Fixpoint.update i;
     | _ -> invalid_arg "set_grammar")
  (*Printf.eprintf "setting %s %b %a\n%!" name ae Charset.print set;*)
  | _ -> invalid_arg "set_grammar"

let grammar_name : type a.a grammar -> string = fun p1 ->
  match snd p1 with
  | [(Next(_,name,_,_,(Empty _,_)),_)] -> name
  | _ -> new_name ()

let char : ?name:string -> char -> 'a -> 'a grammar
  = fun ?name c a ->
    let msg = Printf.sprintf "%C" c in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c', buf', pos' = read buf pos in
      if c = c' then (a,buf',pos') else give_up ()
    in
    solo ~name (Charset.singleton c) fn

let in_charset : ?name:string -> Charset.t -> char grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "[%s]" (Charset.show cs) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c, buf', pos' = read buf pos in
      if Charset.mem cs c then (c,buf',pos') else give_up ()
    in
    solo ~name cs fn

let not_in_charset : ?name:string -> Charset.t -> unit grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "^[%s]" (Charset.show cs) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos =
      let c, buf', pos' = read buf pos in
      if Charset.mem cs c then ((), false) else ((), true)
    in
    test ~name (Charset.complement cs) fn

let blank_not_in_charset : ?name:string -> Charset.t -> unit grammar
  = fun ?name cs ->
    let msg = Printf.sprintf "^[%s]" (Charset.show cs) in
    let name = match name with None -> msg | Some n -> n in
    let fn buf pos _ _ =
      let c, buf', pos' = read buf pos in
      if Charset.mem cs c then ((), false) else ((), true)
    in
    blank_test ~name (Charset.complement cs) fn

let any : char grammar
  = let fn buf pos =
      let c, buf', pos' = read buf pos in
      if c = '\255' then give_up ();
      (c,buf',pos')
    in
    solo ~name:"ANY" Charset.(del full '\255') fn

let debug msg : unit grammar
    = let fn buf pos =
        Printf.eprintf "%s file:%s line:%d col:%d\n%!" msg (filename buf) (line_num buf) pos;
        ((), true)
      in
      test ~name:msg Charset.empty fn

let string : ?name:string -> string -> 'a -> 'a grammar
  = fun ?name s a ->
    let name = match name with None -> s | Some n -> n in
    let fn buf pos =
      let buf = ref buf in
      let pos = ref pos in
      let len_s = String.length s in
      for i = 0 to len_s - 1 do
        let c, buf', pos' = read !buf !pos in
        if c <> s.[i] then give_up ();
        buf := buf'; pos := pos'
      done;
      (a,!buf,!pos)
    in
    solo ~name ~accept_empty:(s="") (Charset.singleton s.[0]) fn

let option : 'a -> 'a grammar -> 'a grammar
  = fun a (_,l) -> mk_grammar ((Empty (Simple a),Container.create())::l)

let regexp : ?name:string -> string -> string array grammar =
  fun ?name str ->
    let name = match name with None -> String.escaped str | Some n -> n in
    let (re, grps) = Regexp.regexp_from_string str in
    let fn buf pos =
      let (buf, pos) = Regexp.read_regexp re buf pos in
      (Array.map (!) grps, buf, pos)
    in
    solo ~name ~accept_empty:(Regexp.accept_empty re)
      (Regexp.accepted_first_chars re) fn

let blank_regexp : string -> blank =
  fun str ->
    let (re, _) = Regexp.regexp_from_string str in
    Regexp.read_regexp re

(* charset is now useless ... will be suppressed soon *)
(*
let black_box : (buffer -> int -> 'a * buffer * int) -> Charset.t -> string -> 'a grammar
  = fun fn set name -> solo ~name set fn
*)
let black_box : (buffer -> int -> 'a * buffer * int) -> Charset.t -> bool -> string -> 'a grammar
  = fun fn set accept_empty name -> solo ~name ~accept_empty set fn

let empty : 'a -> 'a grammar = fun a -> (empty,[(Empty (Simple a), Container.create ())])

let sequence3 : 'a grammar -> 'b grammar -> 'c grammar -> ('a -> 'b -> 'c -> 'd) -> 'd grammar
  = fun l1 l2 l3 f ->
    sequence l1 (sequence l2 l3 (fun x y z -> f z x y)) (fun z f -> f z)

let fsequence : 'a grammar -> ('a -> 'b) grammar -> 'b grammar
  = fun l1 l2 -> mk_grammar [next l1 Idt (grammar_to_rule l2)]

let fsequence_position : 'a grammar -> ('a -> buffer -> int -> buffer -> int -> 'b) grammar -> 'b grammar
  = fun l1 l2 ->
    apply_position idt (fsequence l1 l2)

let conditional_sequence : 'a grammar -> ('a -> 'b) -> 'c grammar -> ('b -> 'c -> 'd) -> 'd grammar
  = fun l1 cond l2 f ->
    mk_grammar [next l1 (Simple cond) (next l2 (Simple (fun b a -> f a b)) idtEmpty)]

let conditional_sequence_position : 'a grammar -> ('a -> 'b) -> 'c grammar -> ('b -> 'c -> buffer -> int -> buffer -> int -> 'd) -> 'd grammar
   = fun l1 cond l2 f ->
     mk_grammar [next l1 (Simple cond)
                  (next l2 Idt (Empty(WithPos(fun b p b' p' a' a -> f a a' b p b' p')),Container.create ()))]

let conditional_fsequence : 'a grammar -> ('a -> 'b) -> ('b -> 'c) grammar -> 'c grammar
  = fun l1 cond l2 ->
    mk_grammar [next l1 (Simple cond) (grammar_to_rule l2)]

let conditional_fsequence_position : 'a grammar -> ('a -> 'b) -> ('b -> buffer -> int -> buffer -> int -> 'c) grammar -> 'c grammar
  = fun l1 cond l2 ->
    apply_position idt (conditional_fsequence l1 cond l2)

let fixpoint :  'a -> ('a -> 'a) grammar -> 'a grammar
  = fun a f1 ->
    let res = declare_grammar "fixpoint" in
    let _ = set_grammar res
      (mk_grammar [(Empty(Simple a),Container.create ());
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
  mk_grammar (List.flatten (List.map snd g))

(* FIXME: optimisation: modify g inside when possible *)
let position g =
  apply_position (fun a buf pos buf' pos' ->
    (filename buf, line_num buf, pos, line_num buf', pos', a)) g

let handle_exception f a =
  try f a with Parse_error(buf, pos, msgs) ->
    begin
      Printf.eprintf "File %S, line %d, character %d:\n"
        (filename buf) (line_num buf) (utf8_col_num buf pos);
      Printf.eprintf "Parse error:\n%!";
      List.iter (Printf.eprintf " - %s\n%!") msgs;
      failwith "No parse."
    end

let grammar_family ?(param_to_string=(fun _ -> "<...>")) name =
  let tbl = EqHashtbl.create ~equal:closure_eq 31 in
  let is_set = ref None in
  (fun p ->
    try EqHashtbl.find tbl p
    with Not_found ->
      let g = declare_grammar (name^"_"^param_to_string p) in
      EqHashtbl.add tbl p g;
      (match !is_set with None -> ()
      | Some f ->
         set_grammar g (f p);
      );
      g),
  (fun f ->
    (*if !is_set <> None then invalid_arg ("grammar family "^name^" already set");*)
    is_set := Some f;
    EqHashtbl.iter (fun p r ->
      set_grammar r (f p);
    ) tbl)

let blank_grammar grammar blank buf pos =
    let save_debug = !debug_lvl in
    debug_lvl := !debug_lvl / 10;
    let (_,buf,pos) = internal_parse_buffer (init_errpos buf pos) grammar blank buf pos in
    debug_lvl := save_debug;
    if !debug_lvl > 0 then Printf.eprintf "exit blank %d %d\n%!" (line_num buf) pos;
    (buf,pos)

let accept_empty grammar =
  try
    ignore (parse_string grammar no_blank ""); true
  with
    Parse_error _ -> false

let change_layout : ?old_blank_before:bool -> ?new_blank_after:bool -> 'a grammar -> blank -> 'a grammar
  = fun ?(old_blank_before=true) ?(new_blank_after=true) l1 blank1 ->
    let i = Fixpoint.from_val (false, Charset.full) in
    (* compose with a test with a full charset to pass the final charset test in
       internal_parse_buffer *)
    let l1 = mk_grammar [next l1 Idt (next (test Charset.full (fun _ _ -> (), true))
                               (Simple (fun _ a -> a)) idtEmpty)] in
    let fn errpos _ buf pos buf' pos' =
      let buf,pos = if old_blank_before then buf', pos' else buf, pos in
      let (a,buf,pos) = internal_parse_buffer errpos l1 blank1
        ~blank_after:new_blank_after buf pos in
      (a,buf,pos)
    in
    greedy_solo i fn

let greedy : 'a grammar -> 'a grammar
  = fun l1 ->
    (* compose with a test with a full charset to pass the final charset test in
       internal_parse_buffer *)
    let l1 = mk_grammar [next l1 Idt (next (test Charset.full (fun _ _ -> (), true))
                                                   (Simple (fun _ a -> a)) idtEmpty)] in
    (* FIXME: blank are parsed twice. internal_parse_buffer should have one more argument *)
    let fn errpos blank buf pos _ _ =
      let (a,buf,pos) = internal_parse_buffer errpos l1 blank buf pos in
      (a,buf,pos)
    in
    greedy_solo (fst l1) fn

let grammar_info : type a. a grammar -> info = fun g -> (force (fst g))

let dependent_sequence : 'a grammar -> ('a -> 'b grammar) -> 'b grammar
  = fun l1 f2 ->
    let tbl = EqHashtbl.create ~equal:closure_eq 31 in
          mk_grammar [next l1 Idt (Dep (fun a ->
              try EqHashtbl.find tbl a
              with Not_found ->
                let res = grammar_to_rule (f2 a) in
                EqHashtbl.add tbl a res; res
          ), Container.create ())]

let iter : 'a grammar grammar -> 'a grammar
  = fun g -> dependent_sequence g (fun x -> x)
