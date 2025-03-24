let _ = Printexc.record_backtrace true

module Int = struct
  type t = int
  let compare = (-)
end

module S1 = Set.Make(Int)
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
  else if size = 1 then S1.singleton (Random.int maxi)
  else S1.add (Random.int maxi) (random_set01 (size - 1) maxi)

let rec random_set1 size maxi =
  if size <= 0 then S1.empty
  else if size = 1 then S1.singleton (Random.int maxi)
  else
    let h1 = size / 2 in
    let h2 = if size mod 2 = 0 then h1 else h1 + 1 in
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
  else if size = 1 then S2.singleton (Random.int maxi)
  else S2.add (Random.int maxi) (random_set02 (size - 1) maxi)

let check2 s =
  S2.iter (fun x -> assert (S2.mem x s)) s

let rec random_set2 size maxi =
  if size <= 0 then S2.empty
  else if size = 1 then S2.singleton (Random.int maxi)
  else
    let h1 = size / 2 in
    let h2 = if size mod 2 = 0 then h1 else h1 + 1 in
    let s1 = random_set2 h1 maxi in
    let s2 = random_set2 h2 maxi in
    S2.union s1 s2

let chrono f a =
  let t0 = Unix.gettimeofday() in
  let x = f a in
  let t1 = Unix.gettimeofday() in
  let dt = t1 -. t0 in
  Printf.printf "%f\n%!" dt;
  (dt, x)

let size = 300_000
let maxi = 100_000_000

let dt1, s1 = chrono order_set1 size
let dt2, s2 = chrono order_set2 size

let _ = Printf.printf "ordered add %f\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2

let _ = Printf.printf "check %f\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let dt1, _ = chrono (order_setr1 size) s1
let dt2, _ = chrono (order_setr2 size) s2

let _ = Printf.printf "ordered rm %f\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let seed = Random.full_int max_int
let _ = Random.init seed
let dt1, s1 = chrono (random_set01 size) maxi
let _ = Random.init seed
let dt2, s2 = chrono (random_set02 size) maxi

let _ = Printf.printf "random add %f\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2

let _ = Printf.printf "check %f\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let seed = Random.full_int max_int
let _ = Random.init seed
let dt1, s1 = chrono (random_set1 size) maxi
let _ = Random.init seed
let dt2, s2 = chrono (random_set2 size) maxi

let _ = Printf.printf "random union %f\n%!" ((dt2 -. dt1) /. dt1 *. 100.)

let dt1, _ = chrono check1 s1
let dt2, _ = chrono check2 s2

let _ = Printf.printf "check %f\n%!" ((dt2 -. dt1) /. dt1 *. 100.)
