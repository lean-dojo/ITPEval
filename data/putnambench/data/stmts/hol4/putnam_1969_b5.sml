(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b5:
  a strictly increasing positive integer sequence with convergent reciprocal
  series has a counting function that is sublinear at positive infinity.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1969_b5 =
  ``!a : num -> num. !k : real -> num.
      (!m n : num. m < n ==> a m < a n) /\
      (!n : num. 0 < a n) /\
      (?L : real.
         ((\N : num.
             SIGMA
               (\n : num. (1 : real) / &(a n))
               (count N)) --> L) sequentially) /\
      (!x : real. k x = CARD {n : num | &(a n) <= x})
      ==>
      !e : real.
        0 < e
        ==>
        ?B : real.
          !t : real.
            B <= t ==> abs (&(k t) / t - 0) < e``;
