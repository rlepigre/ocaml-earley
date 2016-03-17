

let rec pow ch n = 
  if n = 0 then Printf.fprintf ch "1"
  else (
    Printf.fprintf ch "1 ** ";
    pow ch (n-1))

let rec prod ch n m = 
  if m = 0 then pow ch n 
  else (
    pow ch n;
    Printf.fprintf ch "\n*\n";
    prod ch n (m-1))

let rec sum ch n m p = 
  if p = 0 then prod ch n m
  else (
    prod ch n m;
    Printf.fprintf ch "\n+\n";
    sum ch n m (p-1))

let _ =
  let basename = "tripple_calc" in
  for i = 1 to 12 do
    let n = truncate ((float i *. 10. *. 100. *. 100.) ** (1./.3.))in
    let ch = open_out (basename ^ string_of_int i) in
    sum ch n n n;
    close_out ch
  done
