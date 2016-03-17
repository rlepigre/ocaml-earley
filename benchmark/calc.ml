
let nb_tests = 1

let with_time f x =
  let open Gc in
  compact ();
  let { minor_words ; top_heap_words} = Gc.quick_stat () in
  let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
  try
    for i = 2 to nb_tests do
      ignore (f x);
    done;
    let r = f x in
    let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
    let { minor_words = minor_words' ; top_heap_words= top_heap_words'} = Gc.quick_stat () in
    (r, (ut' -. ut) +. (st' -. st), minor_words' -. minor_words, top_heap_words' - top_heap_words)
  with e ->
    let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
    Format.eprintf "exception after: %.2fs@." ((ut' -. ut) +. (st' -. st));
    flush stderr;
    raise e

let parse_camlp4 file =
  let ch = open_in file in
  let res = with_time (Camlp4.PreCast.Gram.parse Calc_camlp4.expr Camlp4.PreCast.Loc.ghost) (Stream.of_channel ch) in
  close_in ch;
  res

let parse_yacc file =
  let ch = open_in file in
  let lexbuf = Lexing.from_channel ch in
  let res = with_time (Parser.main Lexer.token) lexbuf in
  close_in ch;
  res

let parse_decap file =
  let ch = open_in file in
  let res = with_time (Decap.parse_channel (Calc_decap.expr Calc_decap.Sum) Calc_decap.blank) ch in
  close_in ch;
  res

let parse_gdecap file =
  let ch = open_in file in
  let res = with_time (Decap.parse_channel (Calc_gdecap.expr Calc_gdecap.Sum) Calc_gdecap.blank) ch in
  close_in ch;
  res

let parse_sdecap file =
  let ch = open_in file in
  let res = with_time (Decap.parse_channel (Calc_sdecap.expr Calc_sdecap.Sum) Calc_sdecap.blank) ch in
  close_in ch;
  res

let _ =
  Printf.printf "size, yacctime, gdecaptime, sdecaptime, decaptime, camlp4time, yaccalloc, gdecapalloc, sdecapalloc, decapalloc, camlp4alloc, yaccmem, gdecapmem, sdecapmem, decapmem, camlp4mem\n%!";
  for i = 1 to 12 do
    let file = "calc_testfiles/tripple_calc" ^ (string_of_int i) in
    let st = Unix.lstat file in
    let size = Unix.(st.st_size) in
    let _, time_yacc, alloc_yacc, mem_yacc = parse_yacc file in
    let _, time_camlp4, alloc_camlp4, mem_camlp4 = parse_camlp4 file in
    let _, time_decap, alloc_decap, mem_decap = parse_decap file in
    let _, time_sdecap, alloc_sdecap, mem_sdecap = parse_sdecap file in
    let _, time_gdecap, alloc_gdecap, mem_gdecap = parse_gdecap file in
    Printf.printf "%d, %f, %f, %f, %f, %f, %f, %f, %f, %f, %f, %d, %d, %d, %d, %d\n%!" size time_yacc time_gdecap time_sdecap time_decap time_camlp4 alloc_yacc alloc_sdecap alloc_gdecap alloc_decap alloc_camlp4 mem_yacc mem_sdecap mem_gdecap mem_decap mem_camlp4
  done

