(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b2:
  for every positive integer n, the product of the first n positive odd
  integers lies strictly between the specified real-power bounds involving e.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_1996_b2 =
  ``!n : num.
      0 < n
      ==>
      let prododd =
        REAL_PROD_IMAGE
          (\i : num. 2 * (&i : real) - 1)
          (IMAGE SUC (count n))
      in
        ((2 * (&n : real) - 1) / exp 1) powr
          ((2 * (&n : real) - 1) / 2) <
          prododd /\
        prododd <
          ((2 * (&n : real) + 1) / exp 1) powr
            ((2 * (&n : real) + 1) / 2)``;
