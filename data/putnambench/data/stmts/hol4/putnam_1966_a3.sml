(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a3:
  a real sequence satisfying x_(n+1) = x_n(1 - x_n) from n = 1 onward,
  with 0 < x_1 < 1, has n x_n tending to 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory;

val putnam_1966_a3 =
  ``!x : num -> real.
      0 < x 1 /\ x 1 < 1 /\
      (!n : num.
         1 <= n
         ==>
         x (n + 1) = x n * (1 - x n))
      ==>
      ((\n : num. &n * x n) --> 1) sequentially``;
