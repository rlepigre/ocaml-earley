open Earley_core
open Earley

let blank_regexp s =
  let re = Str.regexp s in
  let accept_newline = Str.string_match re "\n" 0 && Str.match_end () = 1 in
  let rec fn str pos =
    let (str, pos) = Input.normalize str pos in
    let l = Input.line str in
    if Str.string_match re l pos then
      let pos = Str.match_end () in
      let len = String.length l in
      if accept_newline && pos = len && not (Input.is_empty str pos) then
        fn str pos
      else (str, pos)
    else (str, pos)
  in fn

let regexp : ?name:string -> string -> ((int -> string) -> 'a) -> 'a grammar =
  fun ?name re  a ->
    let r = Str.regexp re in
    let name =
      match name with
      | None      -> String.escaped re
      | Some name -> name
    in
    let set = Charset.copy Charset.empty in
    let found = ref false in
    for i = 0 to 254 do
      let c = Char.chr i in
      let s = String.make 1 c in
      if Str.string_partial_match r s 0 && Str.match_end () > 0 then
        begin
          found := true;
          Charset.addq set c
        end
    done;
    if not !found then failwith "regexp: illegal empty regexp";
    let fn buf pos =
      let l = Input.line buf in
      if pos >= String.length l then give_up ();
      if Str.string_match r l pos then
        let f n = Str.matched_group n l in
        let pos' = Str.match_end () in
        if pos' = pos then give_up ();
        let res = a f in
        (res, buf, pos')
      else give_up ()
    in
    if Str.string_match r "" 0 then
      let f n = Str.matched_group n "" in
      option (a f) (black_box fn set false name)
    else
      black_box fn set false name
