(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a5:
  a universal constant bounds the series of normalized reciprocal partial
  sums for every positive real sequence with convergent reciprocal series.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1964_a5 =
  ``?k : real.
      !a : num -> real.
        (!n : num. 0 < a n) /\
        (?L2 : real.
           (((\N : num.
                SIGMA
                  (\n : num. (1 : real) / a n)
                  (count N)) --> L2) sequentially))
        ==>
        ?L1 L2 : real.
          (((\N : num.
               SIGMA
                 (\n : num.
                    &(n + 1) /
                    SIGMA
                      (\i : num. a i)
                      (count (n + 1)))
                 (count N)) --> L1) sequentially) /\
          (((\N : num.
               SIGMA
                 (\n : num. (1 : real) / a n)
                 (count N)) --> L2) sequentially) /\
          L1 <= k * L2``;
