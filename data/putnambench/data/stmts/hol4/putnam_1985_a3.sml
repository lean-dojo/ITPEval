(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a3:
  the diagonal of the recursively defined real sequences converges to
  exp d - 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory transcTheory;

val putnam_1985_a3 =
  ``!d : real. !a : num -> num -> real.
      (!m : num. a m 0 = d / (2 : real) pow m) /\
      (!m j : num.
         a m (j + 1) = (a m j) pow 2 + 2 * a m j)
      ==>
      ((\n : num. a n n) --> exp d - 1) sequentially``;
