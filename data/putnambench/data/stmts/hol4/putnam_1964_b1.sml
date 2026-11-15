(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b1:
  a positive integer sequence with convergent reciprocal series has a
  counting function for terms at most n whose ratio to n tends to zero.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1964_b1 =
  ``!a b : num -> num.
      (!n : num. 0 < a n) /\
      (?L : real.
         ((\N : num.
             SIGMA
               (\n : num. (1 : real) / &(a n))
               (count N)) --> L) sequentially) /\
      (!n : num. b n = CARD {k : num | a k <= n})
      ==>
      ((\n : num. &(b n) / &n) --> 0) sequentially``;
