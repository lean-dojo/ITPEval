(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_b1:
  the normalized double sum of a quartic polynomial over indices from one
  through n converges to negative one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1981_b1 =
  ``((\n : num.
        (1 / ((&n : real) pow 5)) *
        SIGMA
          (\h : num.
             SIGMA
               (\k : num.
                  5 * (&h : real) pow 4 -
                  18 * (&h : real) pow 2 * (&k : real) pow 2 +
                  5 * (&k : real) pow 4)
               (IMAGE SUC (count n)))
          (IMAGE SUC (count n))) -->
      -(1 : real))
    sequentially``;
