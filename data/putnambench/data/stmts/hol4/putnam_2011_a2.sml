(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a2:
  positive real sequences satisfying the stated recurrence and boundedness
  condition have reciprocal prefix-product series converging to 3/2. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_2011_a2 =
  ``!a b : num -> real.
      (!n : num. 0 < a n /\ 0 < b n) /\
      a 0 = 1 /\
      b 0 = 1 /\
      (!n : num.
         1 <= n
         ==>
         b n = b (n - 1) * a n - 2) /\
      (?B : real. !n : num. abs (b n) <= B)
      ==>
      ((\n : num.
          SIGMA
            (\i : num.
               1 / REAL_PROD_IMAGE a (count (i + 1)))
            (count n)) -->
        (3 / 2))
      sequentially``;
