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

There is a draft article [here](https://raffalli.eu/pdfs/AVL.pdf).

We also provide pop_min_elt and pop_max_elt to get the min/max element and remove it at
the same time.
