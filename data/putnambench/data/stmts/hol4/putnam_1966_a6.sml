(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a6:
  finite nested-radical approximants defined by their triangular recurrence
  have first entries converging to 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory;

val putnam_1966_a6 =
  ``!a : num -> num -> real.
      (!n : num.
         1 <= n
         ==>
         a n n = &n /\
         !m : num.
           1 <= m /\ m < n
           ==>
           a n m = &m * sqrt (1 + a n (m + 1)))
      ==>
      ((\n : num. a n 1) --> 3) sequentially``;
