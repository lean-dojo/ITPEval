(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b1:
  a finite sum of minima of distances from two rational multiples to the
  nearest integers equals the positive integer parameter. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory real_sigmaTheory;
open intrealTheory;

val putnam_1997_b1 =
  ``let dist_to_int =
      \x : real.
        min (x - real_of_int (INT_FLOOR x))
            (real_of_int (INT_FLOOR (x + 1)) - x)
    in
      !n : num.
        0 < n
        ==>
        SIGMA
          (\m : num.
             min
               (dist_to_int ((&m : real) / (6 * (&n : real))))
               (dist_to_int ((&m : real) / (3 * (&n : real)))))
          (IMAGE SUC (count (6 * n - 1))) =
        (&n : real)``;
