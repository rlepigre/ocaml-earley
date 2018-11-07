
let int = Charset.range '0' '9'
let blank = List.fold_left Charset.add Charset.empty_charset [' ';'\t';'\n';'\r']

let regexp ptr =
  let open Input.Regexp in
  read_regexp (Str (Seq [Str (Set blank); Pls (Set int); Str (Set blank)]))

let test_rodolphe () =
  let time = Sys.time () in
  let ch = open_in Sys.argv.(1) in
  let ptr = ref "" in
  try
    while true do
      let line = input_line ch in
      let buf = Input.buffer_from_string line in
      ignore (regexp ptr buf 0);
    (*Printf.printf "%S\n%!" !ptr;*)
    done;
    assert false
  with
  | Assert_failure _ as e -> raise e
  | _ ->
    close_in ch;
    let time' = Sys.time () in
    Printf.printf "rodolphe: %f\n%!" (time' -. time)

let regexp = Str.regexp "\\([ \n\t\r]*[0-9]+[ \n\t\r]*\\)*"

let test_str () =
  let time = Sys.time () in
  let ch = open_in Sys.argv.(1) in
  try
    while true do
      let line = input_line ch in
      assert (Str.string_match regexp line 0)
    done;
    assert false
  with
  | Assert_failure _ as e -> raise e
  | _ ->
    close_in ch;
    let time' = Sys.time () in
    Printf.printf "str: %f\n%!" (time' -. time)

let _ =
  test_str ();
  test_rodolphe ()
