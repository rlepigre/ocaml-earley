open Earley_core
open Input
open Pa_ocaml
open Pa_lexing
let define_directive =
  Str.regexp "[ \t]*define[ \t]*\\([^ \t]*\\)[ \t]*\\([^ \n\t\r]*\\)[ \t]*"
let if_directive = Str.regexp "[ \t]*if"
let ifdef_directive = Str.regexp "[ \t]*if[ \t]*def[ \t]*\\([^ \t]*\\)[ \t]*"
let ifundef_directive =
  Str.regexp "[ \t]*if[ \t]*ndef[ \t]*\\([^ \t]*\\)[ \t]*"
let ifversion_directive =
  Str.regexp
    "[ \t]*if[ \t]*version[ \t]*\\([<>=]*\\)[ \t]*\\([0-9]+\\)[.]\\([0-9]+\\)[ \t]*"
let else_directive = Str.regexp "[ \t]*else[ \t]*"
let elif_directive = Str.regexp "[ \t]*elif[ \t]*"
let endif_directive = Str.regexp "[ \t]*endif[ \t]*"
let line_num_directive =
  Str.regexp "[ \t]*\\([0-9]+\\)[ \t]*\\([\"]\\([^\"]*\\)[\"]\\)?[ \t]*$"
let test_directive fname num line =
  if Str.string_match ifdef_directive line 1
  then
    let macro_name = Str.matched_group 1 line in
    try ignore (Sys.getenv macro_name); true with | Not_found -> false
  else
    if Str.string_match ifundef_directive line 1
    then
      (let macro_name = Str.matched_group 1 line in
       try ignore (Sys.getenv macro_name); false with | Not_found -> true)
    else
      if Str.string_match ifversion_directive line 1
      then
        (let predicat = Str.matched_group 1 line in
         let major' = Str.matched_group 2 line in
         let minor' = Str.matched_group 3 line in
         try
           let predicat =
             match predicat with
             | "<>" -> (<>)
             | "=" -> (=)
             | "<" -> (<)
             | ">" -> (>)
             | "<=" -> (<=)
             | ">=" -> (>=)
             | _ -> raise Exit in
           let version =
             try Sys.getenv "OCAMLVERSION"
             with | Not_found -> Sys.ocaml_version in
           let (major, minor) =
             match Str.split (Str.regexp_string ".") version with
             | major::minor::_ ->
                 let major = int_of_string major in
                 let minor = int_of_string minor in (major, minor)
             | _ -> assert false in
           predicat (major, minor)
             ((int_of_string major'), (int_of_string minor'))
         with
         | _ ->
             (Printf.eprintf "file: %s, line %d: bad predicate version\n%!"
                fname num;
              exit 1))
      else
        (Printf.eprintf "file: %s, line %d: unknown #if directive\n%!" fname
           num;
         exit 1)
module OCamlPP : Preprocessor =
  struct
    type state = bool list
    let initial_state = []
    let active : state -> bool = fun st -> not (List.mem false st)
    let update st name lnum line =
      if (line <> "") && ((line.[0]) = '#')
      then
        (if (Str.string_match define_directive line 1) && (active st)
         then
           let macro_name = Str.matched_group 1 line in
           let value = Str.matched_group 2 line in
           (Unix.putenv macro_name value; (st, name, lnum, false))
         else
           if Str.string_match if_directive line 1
           then (((test_directive name lnum line) :: st), name, lnum, false)
           else
             if Str.string_match elif_directive line 1
             then
               (match st with
                | [] -> pp_error name "unexpected elif directive"
                | _::st ->
                    (((test_directive name lnum line) :: st), name, lnum,
                      false))
             else
               if Str.string_match else_directive line 1
               then
                 (match st with
                  | [] -> pp_error name "unexpected else directive"
                  | b::st -> (((not b) :: st), name, lnum, false))
               else
                 if Str.string_match endif_directive line 1
                 then
                   (match st with
                    | [] -> pp_error name "unexpected endif directive"
                    | _::st -> (st, name, lnum, false))
                 else
                   if Str.string_match line_num_directive line 1
                   then
                     (let lnum = int_of_string (Str.matched_group 1 line) in
                      let name =
                        try Str.matched_group 3 line with | Not_found -> name in
                      (st, name, lnum, false))
                   else (st, name, lnum, (active st)))
      else (st, name, lnum, (active st))
    let check_final st name =
      match st with | [] -> () | _ -> pp_error name "unclosed conditionals"
  end 
module PP = (Earley.WithPP)(OCamlPP)
let _ =
  let spec : (Arg.key * Arg.spec * Arg.doc) list =
    [("--debug", (Arg.Set_int Earley.debug_lvl),
       "Sets the value of \"Earley.debug_lvl\".");
    ("--debug-attach", (Arg.Set debug_attach),
      "Debug ocamldoc comments attachment.")] in
  let usage = Printf.sprintf "usage: %s [options] file" (Sys.argv.(0)) in
  let file = ref None in
  Arg.parse spec (fun s -> file := (Some s)) usage;
  (let ast =
     let (filename, ic) =
       match !file with
       | None -> ("stdin", stdin)
       | Some file -> (file, (open_in file)) in
     let parse = PP.parse_channel ~filename structure ocaml_blank in
     Earley.handle_exception parse ic in
   Format.printf "%a\n%!" Pprintast.structure ast)
