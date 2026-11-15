(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b1:
  the definite integral from 2 to 4 of the stated logarithmic square-root
  quotient has value 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_1987_b1 =
  ``integration$integral (interval [2, 4])
      (\x : real.
         sqrt (ln (9 - x)) /
         (sqrt (ln (9 - x)) + sqrt (ln (x + 3)))) =
    1``;
