(* FILE Borowed from Planck parser combinator *)

(* This is required to call Syntaxerr.report_error correctly. *)
let _ = Location.input_name := ""

(* necessite la librairie UNIX *)
let min_time = 0.01

let run_fork : 'a 'b.('a -> 'b) -> 'a -> 'b = fun f x ->
  let open Unix in
  let chin, chout = pipe () in
  let chin = in_channel_of_descr chin in
  let chout = out_channel_of_descr chout in
  let pid = fork () in
  if pid = 0 then
    begin
      output_value chout (f x);
      close_out chout;
      exit 0
    end
  else
    let res = input_value chin in
    close_in chin; close_out chout;
    res

let _ = Printf.eprintf "TOP: %d\n%!" Gc.((quick_stat ()).top_heap_words)

let with_time f x =
  let time = ref 0.0 in
  let words = ref 0 in
  let res = ref None in
  let count = ref 0 in
  try
    while !time < min_time do
      incr count;
      Gc.full_major ();
      let f () =
        try
          let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
          let res = f x in
          let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
          let words = Gc.((quick_stat ()).top_heap_words) in
          Some(res,(ut' -. ut) +. (st' -. st),  words)
        with e ->
          Printf.eprintf "Uncaught exception: %s\n%!" (Printexc.to_string e);
          None
      in
      match run_fork f () with
      | None -> assert false
      | Some(r,t,w) ->
         time := !time +. t;
         words := !words + w;
         res := Some r
    done;
    let r = match !res with None -> assert false | Some r -> r in
    (r, !time /. float !count, float !words /. float !count)
  with e ->
    flush stderr;
    raise e

module ParserExt = Pa_parser.Ext(Pa_ocaml_prelude.Initial)
module Default = Pa_ocaml.Make(ParserExt)


(* pa_ocaml (DeCaP) *)
let rec parse_implementation path =
  Earley.handle_exception (Earley.parse_file Default.structure Pa_lexing.ocaml_blank) path

let rec parse_interface path =
  Earley.handle_exception (Earley.parse_file Default.signature Pa_lexing.ocaml_blank) path

(* OCaml *)
let parse_implementation_orig f =
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  Location.init lexbuf f;
  let res = Parse.implementation lexbuf in
  close_in ic;
  res

let parse_interface_orig f =
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  Location.init lexbuf f;
  let res = Parse.interface lexbuf in
  close_in ic;
  res

(* Tests *)
let _ =
  let time_sum_orig = ref 0.0 in
  let time_sum_pa_ocaml = ref 0.0 in
  let mem_sum_orig = ref 0.0 in
  let mem_sum_pa_ocaml = ref 0.0 in
  let max_time_orig = ref 0.0 in
  let min_time_orig = ref max_float in

  let print_times time_orig time_pa_ocaml =
    Format.eprintf "x%f (original %f, pa_ocaml %f)@."
      (time_pa_ocaml /. time_orig)
      time_orig time_pa_ocaml
  in
  let print_mem mem_orig mem_pa_ocaml =
    Format.eprintf "x%f (original %f, pa_ocaml %f)@."
      (mem_pa_ocaml /. mem_orig)
      mem_orig mem_pa_ocaml
  in

  let csv = open_out "ocaml.csv" in
  Printf.fprintf csv "file, yacctime, earleytime, yaccmem, earleymem\n";

  Array.iteri (fun i path -> if i <> 0 (*&& Filename.check_suffix path ".ml"*) then begin
    Format.eprintf "%s@." path;
    let time_orig, mem_orig, time_pa_ocaml, mem_pa_ocaml =
      if Filename.check_suffix path ".ml" then
	begin
	  let res, time_orig, mem_orig = with_time parse_implementation_orig path in
	  let plres, time_pa_ocaml, mem_pa_ocaml = with_time parse_implementation path in
	  time_orig, mem_orig, time_pa_ocaml, mem_pa_ocaml
	end
      else if Filename.check_suffix path ".mli" then
	begin
	  let res, time_orig, mem_orig = with_time parse_interface_orig path in
          let plres, time_pa_ocaml, mem_pa_ocaml = with_time parse_interface path in
	  time_orig, mem_orig, time_pa_ocaml, mem_pa_ocaml
	end
      else assert false
    in
    max_time_orig := max !max_time_orig (time_pa_ocaml /. time_orig);
    min_time_orig := min !min_time_orig (time_pa_ocaml /. time_orig);
    time_sum_orig := !time_sum_orig +. time_orig;
    time_sum_pa_ocaml := !time_sum_pa_ocaml +. time_pa_ocaml;
    mem_sum_orig := !mem_sum_orig +. mem_orig;
    mem_sum_pa_ocaml := !mem_sum_pa_ocaml +. mem_pa_ocaml;
    print_times time_orig time_pa_ocaml;
    print_mem mem_orig mem_pa_ocaml;
    Printf.fprintf csv "%s, %f, %f, %f, %f\n"
                   (Filename.basename path)
		   time_orig time_pa_ocaml
		   mem_orig mem_pa_ocaml
    ;

  end) Sys.argv;
  close_out csv;
  prerr_endline "ALL TEST ENDED";
  print_times !time_sum_orig !time_sum_pa_ocaml;
  Printf.printf "min decap/orig: %f max decap/orig: %f\n"
		!min_time_orig !max_time_orig;

  print_mem !mem_sum_orig !mem_sum_pa_ocaml;
