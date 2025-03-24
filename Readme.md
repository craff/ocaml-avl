Proposal for a replacement for AVL in OCaml (Set and Map)
=========================================================

This proposal uses size (number of nodes, hence cardinal of set) instead of height for balancing,
with the constraints that
- size left_son <= 2 * size right_son + 1
- size right_son <= 2 * size left_son + 1

This bring a few advantages:

- O(1) cardinal of set/size of map
- slightly simpler code or at least not more complicated (see below)
- seems faster in many cases (not always and strangly depends
  on compilation options). Use `dune exec ./test.exe` for some
  simple tests.

We propose for now just the code for Set.

The idea in the following recursive balancing function, including its proof
of termination/correctness as comment and the non obvious fact the the top recursive call
is only done at most three times (the inner calls are one smaller set hence not problematic):
```
    let rec join l v r =
      let cl = cardinal l and cr = cardinal r in
      if cl > (cr lsl 1) lor 1 then
        begin
          match l with
          | Empty -> assert false
          | Node{l=ll;r=lr;v=lv;_} ->
             if cardinal lr > cardinal ll then
               (* hypothesis:
	          cll + clr + 1 = cl > 2cr + d
                  cll < clr <= 2cll + d and threfore
                  clr = clrl + clrr + 1
                  clrl <= 2clrr + d
                  clrr <= 2clrl + d

		  We have 2 cll < cll + clr, hence 2 cll <= cll + clr - 1 <= cl - 2
		  Thefore, as a lemme we have

                  cll <= cl / 2 - 1

		  Let us define the size of subtrees:
                  cl' = cll + clrl + 1
                  cr' = cr + clrr + 1

                  We have:
                  cr' < 1/2 cll + 1/2 clr + clrl + (1 - d)/2
                      < 3/2 cll + d/2 + clrl + (1 - d)/2
		      < 3/2 cll + clrl + (1 + d) / 2
                      < 3/2 cl' + d : OK (if d > 0)

                  cl' < clr + 2clrr + 1 + d
		      <= clr + 2clrr + d
                      <= clrl + 3clrr + 1 + d
                      <= 5clrr + 1 + 2 d
		      <= 5 cr' + 2 d - 4: not sufficient

                  but if this is the second tail rec call, we have

                  cl = cll + clr + 1 <= 5 cr + 2 d - 4
                  hence cll <= cl/2 - 1 <= 5/2 cr + d - 3
                  cl' <= 5/2 cr + d - 3 + clrl + 1
                      <= 5/2 cr + 2 clrr + 2 d - 2
                      <= 5/2 cr' + 2 d - 9/2

                  and in the third tail rec call, we have

                  cl = cll + clr + 1 <= 5/2 cr + 2 d - 9/2
                  hence cll <= cl/2 - 1 <= 5/4 cr + d - 13/4
                  cl' <= 5/4 cr + d - 13/4 + clrl + 1
                      <= 5/4 cr + 2 clrr + 2 d - 9/4
                      <= 2 cr' + 2 d - 17/4
		      <= 2 cr' + d if d < 17/4 (so d = 1 to 4 are ok)

		  We can also show that the second inner recursive call
		  join ll lv lrl, only need one tail rec call:

                  indeed we have ll < lr = lrl + lrr + 1
		                    < 3 lrl + 1 + d
				    <= 3 lrl + d

		  hence in the recursive call we have
                  cl = cll + clr + 1 <= 3 cr + d
                  hence cll <= cl/2 - 1
		            <= 3/2 cr + d/2 - 1
		            <= 3/2 cr + d/2 - 1
                  cl' <= 3/2 cr + d/2 + clrl
                      <= 3/2 cr + 2 clrr + 3/2 d
                      <= 2 cr' + 3/2 d - 2

                  This is ok if 1/2 d <= 2, i.e d <= 4
                *)
               begin
                 match lr with
                 | Empty -> assert false
                 | Node{l=lrl;r=lrr;v=lrv;_} ->
                    join (join ll lv lrl) lrv (join lrr v r)
               end
             else
               (* hypothesis:
	          cl = cll + clr + 1 > 2cr + d
		  clr <= cll <= 2 clr + 1

		  Hence:
                  thus 2 cr + d < 2 cll + 1
                  hence cr < cll + 1 - d
		           <= cll - d

		  let cr' = clr + cr + 1
                  we have cr' <= clr + cll + 1 - d
		              <= 2 cll + 1 - d.
			      <  2 cll + d

		  We also have cll <= 2 clr + d < 2 cr' + d.
                *)
               create ll lv (join lr v r)
        end
      else if cr > (cl lsl 1) lor 1 then
        begin
          match r with
          | Empty -> assert false
          | Node{l=rl;r=rr;v=rv;_} ->
             if cardinal rl > cardinal rr then
               begin
                 match rl with
                 | Empty -> assert false
                 | Node{l=rll;r=rlr;v=rlv;_} ->
                    join (join l v rll) rlv (join rlr rv rr)
                 end
               else
                 create (join l v rl) rv rr
        end
      else
        Node{l; v; r; c=cl+cr+1}
```

In the proposed code we have unrolled the tail rec call, join calls bal that calls create,
avoiding some tests.

The fonction creating node contains an assertion that could be remove when
other have checked the proof.

We also provide pop_min_elt and pop_max_elt to get the min/max element and remove it at
the same time.
