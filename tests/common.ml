open Earley

type kind = Quick | Normal | Full | None
let kind = ref None

let output = ref false

let test_cases (a, b, c) =
  match !kind with Quick -> a | Normal -> b | Full -> c | None -> b

let spec = [ ("--debug", Arg.Set_int debug_lvl,
              "set debug lvl");
              ("--quick", Arg.Unit (fun () -> kind := Quick),
	      "quick tests");
	     ("--normal", Arg.Unit (fun () -> kind := Normal),
	      "normal tests");
	     ("--full", Arg.Unit (fun () -> kind := Full),
	      "full tests (very long)");
	     ("--out", Arg.Set output,
	      "output the test string instead of parsing"); ]

let _  = Arg.parse spec
		   (fun _ -> raise (Arg.Bad "extra arguments"))
		   "run unit tests on decap combinators"
