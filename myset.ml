(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Sets over ordered types *)

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

module type S =
  sig
    type elt
    type t
    val empty: t
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val disjoint: t -> t -> bool
    val diff: t -> t -> t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    val min_elt_opt: t -> elt option
    val pop_min_elt: t -> elt * t
    val max_elt: t -> elt
    val max_elt_opt: t -> elt option
    val pop_max_elt: t -> elt * t
    val choose: t -> elt
    val choose_opt: t -> elt option
    val find: elt -> t -> elt
    val find_opt: elt -> t -> elt option
    val find_first: (elt -> bool) -> t -> elt
    val find_first_opt: (elt -> bool) -> t -> elt option
    val find_last: (elt -> bool) -> t -> elt
    val find_last_opt: (elt -> bool) -> t -> elt option
    val iter: (elt -> unit) -> t -> unit
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val map: (elt -> elt) -> t -> t
    val filter: (elt -> bool) -> t -> t
    val filter_map: (elt -> elt option) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val split: elt -> t -> t * bool * t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val equal: t -> t -> bool
    val compare: t -> t -> int
    val subset: t -> t -> bool
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val to_list : t -> elt list
    val of_list: elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val to_rev_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t
    val stat : t -> int * int * float
  end

module Make(Ord: OrderedType) =
  struct
    type elt = Ord.t
    type t = Empty | Node of {l:t; v:elt; r:t; c:int}

    (* Sets are represented by balanced binary trees (the size of the
       children differ by a factor at most 2 + 1. More precisely
       cardinal l <= 2 * cardinal r + 1
       cardinal r <= 2 * cardinal l + 1 *)

    let cardinal = function
        Empty -> 0
      | Node {c; _} -> c

    (* Creates a new node with left son l, value v and right son r.
       We must have all elements of l < v < all elements of r.
       l and r must be balanced and | height l - height r | <= 2.
       Inline expansion of height for better speed. *)

    let create l v r =
      let cl = match l with Empty -> 0 | Node {c; _} -> c in
      let cr = match r with Empty -> 0 | Node {c; _} -> c in
      (* TO DO: remove assertion when we are sure *)
      assert (cl <= 2 * cr + 3 && cr <= 2 * cl + 3);
      Node{l; v; r; c=cl+cr+1}

    (* Same as create, but performs rebalancing if necessary.
       Assumes nothing: thanks to the 3 recursive calls max at toplevel
       see Readme.md.

       Inline expansion of create for better speed in the most frequent case
       where no rebalancing is required. *)

    let rec join l v r =
      let cl = cardinal l and cr = cardinal r in
      if cl > (cr lsl 1) + 3 then
        begin
          match l with
          | Empty -> assert false
          | Node{l=ll;r=lr;v=lv;_} ->
             if cardinal lr > cardinal ll then
               begin
                 match lr with
                 | Empty -> assert false
                 | Node{l=lrl;r=lrr;v=lrv;_} ->
                    bal (bal ll lv lrl) lrv (join lrr v r)
               end
             else
               create ll lv (join lr v r)
        end
      else if cr > (cl lsl 1) + 3 then
        begin
          match r with
          | Empty -> assert false
          | Node{l=rl;r=rr;v=rv;_} ->
             if cardinal rl > cardinal rr then
               begin
                 match rl with
                 | Empty -> assert false
                 | Node{l=rll;r=rlr;v=rlv;_} ->
                    bal (join l v rll) rlv (bal rlr rv rr)
                 end
               else
                 create (join l v rl) rv rr
        end
      else
        Node{l; v; r; c=cl+cr+1}

    and bal l v r =
      let cl = cardinal l and cr = cardinal r in
      if cl > (cr lsl 1) + 3 then
        begin
          match l with
          | Empty -> assert false
          | Node{l=ll;r=lr;v=lv;_} ->
             if cardinal lr > cardinal ll then
               begin
                 match lr with
                 | Empty -> assert false
                 | Node{l=lrl;r=lrr;v=lrv;_} ->
                    create (bal ll lv lrl) lrv (join lrr v r)
               end
             else
               create ll lv (join lr v r)
        end
      else if cr > (cl lsl 1) + 3 then
        begin
          match r with
          | Empty -> assert false
          | Node{l=rl;r=rr;v=rv;_} ->
             if cardinal rl > cardinal rr then
               begin
                 match rl with
                 | Empty -> assert false
                 | Node{l=rll;r=rlr;v=rlv;_} ->
                    create (join l v rll) rlv (bal rlr rv rr)
                 end
               else
                 create (join l v rl) rv rr
        end
      else
        Node{l; v; r; c=cl+cr+1}

    (* Insertion of one element *)

    let rec add x = function
        Empty -> Node{l=Empty; v=x; r=Empty; c=1}
      | Node{l; v; r; _} as t ->
          let c = Ord.compare x v in
          if c = 0 then t else
          if c < 0 then
            let ll = add x l in
            if l == ll then t else bal ll v r
          else
            let rr = add x r in
            if r == rr then t else bal l v rr

    let singleton x = Node{l=Empty; v=x; r=Empty; c=1}

     (* Smallest and greatest element of a set *)

    let rec min_elt = function
        Empty -> raise Not_found
      | Node{l=Empty; v; _} -> v
      | Node{l; _} -> min_elt l

    let rec min_elt_opt = function
        Empty -> None
      | Node{l=Empty; v; _} -> Some v
      | Node{l; _} -> min_elt_opt l

    let rec max_elt = function
        Empty -> raise Not_found
      | Node{v; r=Empty; _} -> v
      | Node{r; _} -> max_elt r

    let rec max_elt_opt = function
        Empty -> None
      | Node{v; r=Empty; _} -> Some v
      | Node{r; _} -> max_elt_opt r

    (* Remove the smallest element of the given set *)

    let rec pop_min_elt = function
        Empty -> raise Not_found
      | Node{l=Empty; v; r; _} -> (v, r)
      | Node{l; r; _} -> let (v, l) = pop_min_elt l in
                         (v, bal l v r)

    let rec pop_max_elt = function
        Empty -> raise Not_found
      | Node{l; v; r=Empty; _} -> (v, l)
      | Node{l; r; _} -> let (v, r) = pop_max_elt r in
                         (v, bal l v r)

    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
           let (v, r) = pop_min_elt t2 in
           join t1 v r

    (* Splitting.  split x s returns a triple (l, present, r) where
        - l is the set of elements of s that are < x
        - r is the set of elements of s that are > x
        - present is false if s contains no element equal to x,
          or true if s contains an element equal to x. *)

    let rec split x = function
        Empty ->
          (Empty, false, Empty)
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then (l, true, r)
          else if c < 0 then
            let (ll, pres, rl) = split x l in (ll, pres, join rl v r)
          else
            let (lr, pres, rr) = split x r in (join l v lr, pres, rr)

    (* Implementation of the set operations *)

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec mem x = function
        Empty -> false
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          c = 0 || mem x (if c < 0 then l else r)

    let rec remove x = function
        Empty -> Empty
      | (Node{l; v; r; _} as t) ->
          let c = Ord.compare x v in
          if c = 0 then concat l r
          else
            if c < 0 then
              let ll = remove x l in
              if l == ll then t
              else bal ll v r
            else
              let rr = remove x r in
              if r == rr then t
              else bal l v rr

    let rec union s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> t2
      | (t1, Empty) -> t1
      | (Node{l=l1; v=v1; r=r1; c=c1}, Node{l=l2; v=v2; r=r2; c=c2}) ->
          if  c1 >= c2 then
            if c2 = 1 then add v2 s1 else begin
              let (l2, _, r2) = split v1 s2 in
              join (union l1 l2) v1 (union r1 r2)
            end
          else
            if c1 = 1 then add v1 s2 else begin
              let (l1, _, r1) = split v2 s1 in
              join (union l1 l2) v2 (union r1 r2)
            end

    let rec inter s1 s2 =
      match (s1, s2) with
        (Empty, _) -> Empty
      | (_, Empty) -> Empty
      | (Node{l=l1; v=v1; r=r1; _}, t2) ->
          match split v1 t2 with
            (l2, false, r2) ->
              concat (inter l1 l2) (inter r1 r2)
          | (l2, true, r2) ->
              join (inter l1 l2) v1 (inter r1 r2)

    (* Same as split, but compute the left and right subtrees
       only if the pivot element is not in the set.  The right subtree
       is computed on demand. *)

    type split_bis =
      | Found
      | NotFound of t * (unit -> t)

    let rec split_bis x = function
        Empty ->
          NotFound (Empty, (fun () -> Empty))
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then Found
          else if c < 0 then
            match split_bis x l with
            | Found -> Found
            | NotFound (ll, rl) -> NotFound (ll, (fun () -> join (rl ()) v r))
          else
            match split_bis x r with
            | Found -> Found
            | NotFound (lr, rr) -> NotFound (join l v lr, rr)

    let rec disjoint s1 s2 =
      match (s1, s2) with
        (Empty, _) | (_, Empty) -> true
      | (Node{l=l1; v=v1; r=r1; _}, t2) ->
          if s1 == s2 then false
          else match split_bis v1 t2 with
              NotFound(l2, r2) -> disjoint l1 l2 && disjoint r1 (r2 ())
            | Found -> false

    let rec diff s1 s2 =
      match (s1, s2) with
        (Empty, _) -> Empty
      | (t1, Empty) -> t1
      | (Node{l=l1; v=v1; r=r1; _}, t2) ->
          match split v1 t2 with
            (l2, false, r2) ->
              join (diff l1 l2) v1 (diff r1 r2)
          | (l2, true, r2) ->
              concat (diff l1 l2) (diff r1 r2)

    type enumeration = End | More of elt * t * enumeration

    let rec cons_enum s e =
      match s with
        Empty -> e
      | Node{l; v; r; _} -> cons_enum l (More(v, r, e))

    let rec compare_aux e1 e2 =
        match (e1, e2) with
        (End, End) -> 0
      | (End, _)  -> -1
      | (_, End) -> 1
      | (More(v1, r1, e1), More(v2, r2, e2)) ->
          let c = Ord.compare v1 v2 in
          if c <> 0
          then c
          else compare_aux (cons_enum r1 e1) (cons_enum r2 e2)

    let compare s1 s2 =
      compare_aux (cons_enum s1 End) (cons_enum s2 End)

    let equal s1 s2 =
      compare s1 s2 = 0

    let rec subset s1 s2 =
      match (s1, s2) with
        Empty, _ ->
          true
      | _, Empty ->
          false
      | Node {l=l1; v=v1; r=r1; _}, (Node {l=l2; v=v2; r=r2; _} as t2) ->
          let c = Ord.compare v1 v2 in
          if c = 0 then
            subset l1 l2 && subset r1 r2
          else if c < 0 then
            subset (Node {l=l1; v=v1; r=Empty; c=0}) l2 && subset r1 t2
          else
            subset (Node {l=Empty; v=v1; r=r1; c=0}) r2 && subset l1 t2

    let rec iter f = function
        Empty -> ()
      | Node{l; v; r; _} -> iter f l; f v; iter f r

    let rec fold f s accu =
      match s with
        Empty -> accu
      | Node{l; v; r; _} -> fold f r (f v (fold f l accu))

    let rec for_all p = function
        Empty -> true
      | Node{l; v; r; _} -> p v && for_all p l && for_all p r

    let rec exists p = function
        Empty -> false
      | Node{l; v; r; _} -> p v || exists p l || exists p r

    let rec filter p = function
        Empty -> Empty
      | (Node{l; v; r; _}) as t ->
          (* call [p] in the expected left-to-right order *)
          let l' = filter p l in
          let pv = p v in
          let r' = filter p r in
          if pv then
            if l==l' && r==r' then t else join l' v r'
          else concat l' r'

    let rec partition p = function
        Empty -> (Empty, Empty)
      | Node{l; v; r; _} ->
          (* call [p] in the expected left-to-right order *)
          let (lt, lf) = partition p l in
          let pv = p v in
          let (rt, rf) = partition p r in
          if pv
          then (join lt v rt, concat lf rf)
          else (concat lt rt, join lf v rf)

    let rec elements_aux accu = function
        Empty -> accu
      | Node{l; v; r; _} -> elements_aux (v :: elements_aux accu r) l

    let elements s =
      elements_aux [] s

    let choose = min_elt

    let choose_opt = min_elt_opt

    let rec find x = function
        Empty -> raise Not_found
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then v
          else find x (if c < 0 then l else r)

    let rec find_first_aux v0 f = function
        Empty ->
          v0
      | Node{l; v; r; _} ->
          if f v then
            find_first_aux v f l
          else
            find_first_aux v0 f r

    let rec find_first f = function
        Empty ->
          raise Not_found
      | Node{l; v; r; _} ->
          if f v then
            find_first_aux v f l
          else
            find_first f r

    let rec find_first_opt_aux v0 f = function
        Empty ->
          Some v0
      | Node{l; v; r; _} ->
          if f v then
            find_first_opt_aux v f l
          else
            find_first_opt_aux v0 f r

    let rec find_first_opt f = function
        Empty ->
          None
      | Node{l; v; r; _} ->
          if f v then
            find_first_opt_aux v f l
          else
            find_first_opt f r

    let rec find_last_aux v0 f = function
        Empty ->
          v0
      | Node{l; v; r; _} ->
          if f v then
            find_last_aux v f r
          else
            find_last_aux v0 f l

    let rec find_last f = function
        Empty ->
          raise Not_found
      | Node{l; v; r; _} ->
          if f v then
            find_last_aux v f r
          else
            find_last f l

    let rec find_last_opt_aux v0 f = function
        Empty ->
          Some v0
      | Node{l; v; r; _} ->
          if f v then
            find_last_opt_aux v f r
          else
            find_last_opt_aux v0 f l

    let rec find_last_opt f = function
        Empty ->
          None
      | Node{l; v; r; _} ->
          if f v then
            find_last_opt_aux v f r
          else
            find_last_opt f l

    let rec find_opt x = function
        Empty -> None
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then Some v
          else find_opt x (if c < 0 then l else r)

    let try_join l v r =
      (* [join l v r] can only be called when (elements of l < v <
         elements of r); use [try_join l v r] when this property may
         not hold, but you hope it does hold in the common case *)
      if (l = Empty || Ord.compare (max_elt l) v < 0)
      && (r = Empty || Ord.compare v (min_elt r) < 0)
      then join l v r
      else union l (add v r)

    let rec map f = function
      | Empty -> Empty
      | Node{l; v; r; _} as t ->
         (* enforce left-to-right evaluation order *)
         let l' = map f l in
         let v' = f v in
         let r' = map f r in
         if l == l' && v == v' && r == r' then t
         else try_join l' v' r'

    let try_concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
         let (v, r) = pop_min_elt t2 in
         try_join t1 v r

    let rec filter_map f = function
      | Empty -> Empty
      | Node{l; v; r; _} as t ->
         (* enforce left-to-right evaluation order *)
         let l' = filter_map f l in
         let v' = f v in
         let r' = filter_map f r in
         begin match v' with
           | Some v' ->
              if l == l' && v == v' && r == r' then t
              else try_join l' v' r'
           | None ->
              try_concat l' r'
         end

    let of_sorted_list l =
      let rec sub n l =
        match n, l with
        | 0, l -> Empty, l
        | 1, x0 :: l -> Node {l=Empty; v=x0; r=Empty; c=1}, l
        | 2, x0 :: x1 :: l ->
            Node{l=Node{l=Empty; v=x0; r=Empty; c=1}; v=x1; r=Empty; c=2}, l
        | 3, x0 :: x1 :: x2 :: l ->
            Node{l=Node{l=Empty; v=x0; r=Empty; c=1}; v=x1;
                 r=Node{l=Empty; v=x2; r=Empty; c=1}; c=3}, l
        | n, l ->
          let nl = n / 2 in
          let left, l = sub nl l in
          match l with
          | [] -> assert false
          | mid :: l ->
            let right, l = sub (n - nl - 1) l in
            create left mid right, l
      in
      fst (sub (List.length l) l)

    let to_list = elements

    let of_list l =
      match l with
      | [] -> empty
      | [x0] -> singleton x0
      | [x0; x1] -> add x1 (singleton x0)
      | [x0; x1; x2] -> add x2 (add x1 (singleton x0))
      | [x0; x1; x2; x3] -> add x3 (add x2 (add x1 (singleton x0)))
      | [x0; x1; x2; x3; x4] -> add x4 (add x3 (add x2 (add x1 (singleton x0))))
      | _ -> of_sorted_list (List.sort_uniq Ord.compare l)

    let add_seq i m =
      Seq.fold_left (fun s x -> add x s) m i

    let of_seq i = add_seq i empty

    let rec seq_of_enum_ c () = match c with
      | End -> Seq.Nil
      | More (x, t, rest) -> Seq.Cons (x, seq_of_enum_ (cons_enum t rest))

    let to_seq c = seq_of_enum_ (cons_enum c End)

    let rec snoc_enum s e =
      match s with
        Empty -> e
      | Node{l; v; r; _} -> snoc_enum r (More(v, l, e))

    let rec rev_seq_of_enum_ c () = match c with
      | End -> Seq.Nil
      | More (x, t, rest) -> Seq.Cons (x, rev_seq_of_enum_ (snoc_enum t rest))

    let to_rev_seq c = rev_seq_of_enum_ (snoc_enum c End)

    let to_seq_from low s =
      let rec aux low s c = match s with
        | Empty -> c
        | Node {l; r; v; _} ->
            begin match Ord.compare v low with
              | 0 -> More (v, r, c)
              | n when n<0 -> aux low r c
              | _ -> aux low l (More (v, r, c))
            end
      in
      seq_of_enum_ (aux low s End)

    let stat t =
      let mini = ref max_int in
      let maxi = ref (-1) in
      let sum = ref 0 in
      let nb = ref 0 in
      let rec fn h = function
        | Empty ->
           mini := min h !mini;
           maxi := max h !maxi;
           sum  := !sum + h;
           incr nb
        | Node{l;r;_} ->
           fn (h+1) l; fn (h+1) r
      in
      fn 0 t;
      (!mini, !maxi, float !sum /. float !nb)

  end
