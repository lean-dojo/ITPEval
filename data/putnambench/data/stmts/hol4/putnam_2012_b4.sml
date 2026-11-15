(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b4:
  the recurrence a 0 = 1 and a (n + 1) = a n + exp (-a n) yields a finite
  real limit for a n - ln n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory transcTheory;

val putnam_2012_b4 =
  ``!a : num -> real.
      a 0 = 1 /\
      (!n : num. a (n + 1) = a n + exp (-a n))
      ==>
      ?L : real.
        ((\n : num. a n - ln (&n : real)) --> L) sequentially``;
