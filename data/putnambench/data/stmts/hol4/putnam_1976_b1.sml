(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b1:
  the normalized sum of the differences between two related floor quotients
  converges to ln 4 - 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory real_sigmaTheory;
open intrealTheory real_topologyTheory transcTheory;

val putnam_1976_b1 =
  ``((\n : num.
       1 / (&n : real) *
       SIGMA
         (\k : num.
            real_of_int
              (INT_FLOOR (2 * (&n : real) / (&k : real)) -
               2 * INT_FLOOR ((&n : real) / (&k : real))))
         (IMAGE SUC (count n))) -->
     (ln 4 - 1 : real))
    sequentially``;
