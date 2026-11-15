(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a4:
  a real sequence whose two-step differences tend to zero has its one-step
  differences divided by the index tend to zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory;

val putnam_1970_a4 =
  ``!x : num -> real.
      ((\n : num. x n - x (n - 2)) --> 0) sequentially
      ==>
      ((\n : num. (x n - x (n - 1)) / &n) --> 0) sequentially``;
