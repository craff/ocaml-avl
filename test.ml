let _ = Printexc.record_backtrace true

module Int = struct
  type t = int
  let compare = (-)
end

module S1 = Oriset.Make(Int)
module S2 = Myset.Make(Int)
module S3 = Baby.H.Set.Make(Int)
module S4 = Baby.W.Set.Make(Int)


let rec order_set1 size =
  if size <= 0 then S1.empty
  else if size = 1 then S1.singleton size
  else S1.add size (order_set1 (size - 1))

let rec order_setr1 size s =
  if size <= 0 then assert (S1.is_empty s)
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
  if size <= 0 then assert (S2.is_empty s)
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

let rec order_set3 size =
  if size <= 0 then S3.empty
  else if size = 1 then S3.singleton size
  else S3.add size (order_set3 (size - 1))

let rec order_setr3 size s =
  if size <= 0 then assert (S3.is_empty s)
  else order_setr3 (size - 1) (S3.remove size s)

let rec random_set03 size maxi =
  if size <= 0 then S3.empty
  else if size = 1 then S3.singleton (Random.full_int maxi)
  else S3.add (Random.full_int maxi) (random_set03 (size - 1) maxi)

let check3 s =
  S3.iter (fun x -> assert (S3.mem x s)) s

let rec random_set3 size maxi =
  if size < 0 then invalid_arg "random_set3";
  if size = 0 then S3.empty
  else if size = 1 then S3.singleton (Random.full_int maxi)
  else
    let h1 = Random.int (size+1) in
    let h2 = size - h1 in
    let s1 = random_set3 h1 maxi in
    let s2 = random_set3 h2 maxi in
    S3.union s1 s2

let rec order_set4 size =
  if size <= 0 then S4.empty
  else if size = 1 then S4.singleton size
  else S4.add size (order_set4 (size - 1))

let rec order_setr4 size s =
  if size <= 0 then assert (S4.is_empty s)
  else order_setr4 (size - 1) (S4.remove size s)

let rec random_set04 size maxi =
  if size <= 0 then S4.empty
  else if size = 1 then S4.singleton (Random.full_int maxi)
  else S4.add (Random.full_int maxi) (random_set04 (size - 1) maxi)

let check4 s =
  S4.iter (fun x -> assert (S4.mem x s)) s

let rec random_set4 size maxi =
  if size < 0 then invalid_arg "random_set4";
  if size = 0 then S4.empty
  else if size = 1 then S4.singleton (Random.full_int maxi)
  else
    let h1 = Random.int (size+1) in
    let h2 = size - h1 in
    let s1 = random_set4 h1 maxi in
    let s2 = random_set4 h2 maxi in
    S4.union s1 s2

let ori = ref 0

let fake _ = (0, 0, 0.0)

let chrono ?(stat=fake) f a =
  let t0 = Unix.gettimeofday() in
  let x = f a in
  let t1 = Unix.gettimeofday() in
  let dt = t1 -. t0 in
  let msg = match !ori with
    | 0 -> "OCaml's set: "
    | 1 -> "Proposal set: "
    | 2 -> "Baby H Set: "
    | 3 -> "Baby W Set: "
    | _ -> assert false
  in
  ori := (!ori + 1) mod 4;
  let mi, ma, av = stat x in
  if ma <> 0 then
    Printf.printf "%s: %.5fs, branches: (min: %d, max: %d, avg: %.2f)\n%!"
      msg dt mi ma av
  else
    Printf.printf "%s: %.5fs\n%!" msg dt;
  (dt, x)

let size = if Array.length Sys.argv >= 2 then
             int_of_string Sys.argv.(1)
           else 200_000
let maxi = max_int

let _ = Printf.printf "Adding %d consecutive integers in a set:\n" size

let dt1, s1 = chrono ~stat:S1.stat order_set1 size
let dt2, s2 = chrono ~stat:S2.stat order_set2 size
let dt3, s3 = chrono               order_set3 size
let dt4, s4 = chrono               order_set4 size

let _ = Printf.printf "Variation for ordered add: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Checking mem on all elements of the above:\n"

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2
let dt3, _ = chrono check3 s3
let dt4, _ = chrono check4 s4

let _ = Printf.printf "Variation for check mem: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Removing all elements of the above:\n"

let dt1, _ = chrono (order_setr1 size) s1
let dt2, _ = chrono (order_setr2 size) s2
let dt3, _ = chrono (order_setr3 size) s3
let dt4, _ = chrono (order_setr4 size) s4

let _ = Printf.printf "Variation for ordered rm: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "\nAdding %d random integers in a set:\n" size

let seed = Random.full_int max_int
let _ = Random.init seed
let dt1, s1 = chrono ~stat:S1.stat (random_set01 size) maxi
let _ = Random.init seed
let dt2, s2 = chrono ~stat:S2.stat (random_set02 size) maxi
let _ = Random.init seed
let dt3, s3 = chrono               (random_set03 size) maxi
let _ = Random.init seed
let dt4, s4 = chrono               (random_set04 size) maxi

let _ = Printf.printf "Variation for random add: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let elts1 = S1.elements s1
let elts2 = S2.elements s2
let elts3 = S3.elements s3
let elts4 = S4.elements s4

let _ = assert (elts1 = elts2)
let _ = assert (elts1 = elts3)
let _ = assert (elts1 = elts4)

let _ = Printf.printf "Checking mem on all elements of the above:\n"

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2
let dt3, _ = chrono check3 s3
let dt4, _ = chrono check4 s4

let _ = Printf.printf "Variation for check mem: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Removing all elements of the above:\n"

let dt1, _ = chrono (List.fold_left (fun s x -> S1.remove x s) s1) elts1
let dt2, _ = chrono (List.fold_left (fun s x -> S2.remove x s) s2) elts2
let dt3, _ = chrono (List.fold_left (fun s x -> S3.remove x s) s3) elts3
let dt4, _ = chrono (List.fold_left (fun s x -> S4.remove x s) s4) elts4

let _ = Printf.printf "Variation for random rm: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "\nBuilding set of ~%d elements by random union:\n" size

let seed = Random.full_int max_int
let _ = Random.init seed
let dt1, s1 = chrono ~stat:S1.stat (random_set1 size) maxi
let _ = Random.init seed
let dt2, s2 = chrono ~stat:S2.stat (random_set2 size) maxi
let _ = Random.init seed
let dt3, s3 = chrono               (random_set3 size) maxi
let _ = Random.init seed
let dt4, s4 = chrono               (random_set4 size) maxi

let _ = Printf.printf "Variation for random union: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let elts1 = S1.elements s1
let elts2 = S2.elements s2
let elts3 = S3.elements s3
let elts4 = S4.elements s4

let _ = assert (elts1 = elts2)
let _ = assert (elts1 = elts3)
let _ = assert (elts1 = elts4)

let _ = Printf.printf "Checking mem on all elements of the above:\n"

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2
let dt3, _ = chrono check3 s3
let dt4, _ = chrono check4 s4

let _ = Printf.printf "Variation for check mem: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)

let _ = Printf.printf "Removing all elements of the above:\n"

let dt1, _ = chrono (List.fold_left (fun s x -> S1.remove x s) s1) elts1
let dt2, _ = chrono (List.fold_left (fun s x -> S2.remove x s) s2) elts2
let dt3, _ = chrono (List.fold_left (fun s x -> S3.remove x s) s3) elts3
let dt4, _ = chrono (List.fold_left (fun s x -> S4.remove x s) s4) elts4

let _ = Printf.printf "Variation for random union rm: Ours: %.2f%% Baby H: %.2f%% Baby W: %.2f%%\n%!"
          ((dt2 -. dt1) /. dt1 *. 100.)
          ((dt3 -. dt1) /. dt1 *. 100.)
          ((dt4 -. dt1) /. dt1 *. 100.)
