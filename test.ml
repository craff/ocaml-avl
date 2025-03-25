let _ = Printexc.record_backtrace true

module Int = struct
  type t = int
  let compare = (-)
end

module S1 = Oriset.Make(Int)
module S2 = Myset.Make(Int)

let rec order_set1 size =
  if size <= 0 then S1.empty
  else if size = 1 then S1.singleton size
  else S1.add size (order_set1 (size - 1))

let rec order_setr1 size s =
  if size <= 0 then s
  else order_setr1 (size - 1) (S1.remove size s)

let rec random_set01 size maxi =
  if size <= 0 then S1.empty
  else if size = 1 then S1.singleton (Random.full_int maxi)
  else S1.add (Random.full_int maxi) (random_set01 (size - 1) maxi)

let rec random_set1 size maxi =
  if size < 0 then invalid_arg "random_set1";
  if size = 0 then S1.empty
  else if size = 1 then S1.singleton (Random.full_int maxi)
  else
    let h1 = Random.full_int (size+1) in
    let h2 = size - h1 in
    let s1 = random_set1 h1 maxi in
    let s2 = random_set1 h2 maxi in
    S1.union s1 s2

let check1 s =
  S1.iter (fun x -> assert (S1.mem x s)) s

let rec order_set2 size =
  if size <= 0 then S2.empty
  else if size = 1 then S2.singleton size
  else S2.add size (order_set2 (size - 1))

let rec order_setr2 size s =
  if size <= 0 then s
  else order_setr2 (size - 1) (S2.remove size s)

let rec random_set02 size maxi =
  if size <= 0 then S2.empty
  else if size = 1 then S2.singleton (Random.full_int maxi)
  else S2.add (Random.full_int maxi) (random_set02 (size - 1) maxi)

let check2 s =
  S2.iter (fun x -> assert (S2.mem x s)) s

let rec random_set2 size maxi =
  if size < 0 then invalid_arg "random_set2";
  if size = 0 then S2.empty
  else if size = 1 then S2.singleton (Random.full_int maxi)
  else
    let h1 = Random.int (size+1) in
    let h2 = size - h1 in
    let s1 = random_set2 h1 maxi in
    let s2 = random_set2 h2 maxi in
    S2.union s1 s2

let ori = ref true

let fake _ = (0, 0, 0.0)

let chrono ?(stat=fake) f a =
  let t0 = Unix.gettimeofday() in
  let x = f a in
  let t1 = Unix.gettimeofday() in
  let dt = t1 -. t0 in
  let msg = if !ori then "OCaml's set: " else "Proposal set: " in
  ori := not !ori;
  let mi, ma, av = stat x in
  if ma <> 0 then
    Printf.printf "%s: %.5fs, branches: (min: %d, max: %d, avg: %.1f)\n%!"
      msg dt mi ma av
  else
    Printf.printf "%s: %.5fs\n%!" msg dt;
  (dt, x)

let size = 200_000
let maxi = max_int

let _ = Printf.printf "Adding %d consecutive integers in a set:\n" size

let dt1, s1 = chrono ~stat:S1.stat order_set1 size
let dt2, s2 = chrono ~stat:S2.stat order_set2 size

let _ = Printf.printf "ordered add %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Checking mem on all elements of the above:\n"

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2

let _ = Printf.printf "check mem %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Removing all elements of the above:\n"

let dt1, _ = chrono (order_setr1 size) s1
let dt2, _ = chrono (order_setr2 size) s2

let _ = Printf.printf "ordered rm %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "\nAdding %d random integers in a set:\n" size

let seed = Random.full_int max_int
let _ = Random.init seed
let dt1, s1 = chrono ~stat:S1.stat (random_set01 size) maxi
let _ = Random.init seed
let dt2, s2 = chrono ~stat:S2.stat (random_set02 size) maxi

let _ = Printf.printf "random add %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let elts1 = S1.elements s1
let elts2 = S2.elements s2

let _ = assert (elts1 = elts2)

let _ = Printf.printf "Checking mem on all elements of the above:\n"

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2

let _ = Printf.printf "check mem %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Removing all elements of the above:\n"

let dt1, _ = chrono (List.fold_left (fun s x -> S1.remove x s) s1) elts1
let dt2, _ = chrono (List.fold_left (fun s x -> S2.remove x s) s2) elts2

let _ = Printf.printf "random rm %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "\nBuilding set of ~%d elements by random union:\n" size

let seed = Random.full_int max_int
let _ = Random.init seed
let dt1, s1 = chrono ~stat:S1.stat (random_set1 size) maxi
let _ = Random.init seed
let dt2, s2 = chrono ~stat:S2.stat (random_set2 size) maxi

let _ = Printf.printf "random union %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let elts1 = S1.elements s1
let elts2 = S2.elements s2

let _ = assert (elts1 = elts2)

let _ = Printf.printf "Checking mem on all elements of the above:\n"

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2

let _ = Printf.printf "check mem %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Removing all elements of the above:\n"

let dt1, _ = chrono (List.fold_left (fun s x -> S1.remove x s) s1) elts1
let dt2, _ = chrono (List.fold_left (fun s x -> S2.remove x s) s2) elts2

let _ = Printf.printf "random union rm %.2f%%\n%!" ((dt2 -. dt1) /. dt1 *. 100.)
