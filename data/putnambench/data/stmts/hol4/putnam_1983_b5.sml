(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b5:
  the limit of a normalized integral of the distance from n/x to the nearest
  integer, assuming the Wallis product limit. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory real_sigmaTheory;
open intrealTheory real_topologyTheory transcTheory integrationTheory;

val putnam_1983_b5 =
  ``let dist =
      \x : real.
        min (x - real_of_int (INT_FLOOR x))
            (real_of_int (INT_FLOOR (x + 1)) - x)
    in
      (((\N : num.
           REAL_PROD_IMAGE
             (\k : num.
                (2 * (&k : real) / (2 * (&k : real) - 1)) *
                (2 * (&k : real) / (2 * (&k : real) + 1)))
             (IMAGE SUC (count N))) -->
         (pi / 2 : real))
        sequentially)
      ==>
      (((\n : num.
           1 / (&n : real) *
           integration$integral (interval [1, (&n : real)])
             (\x : real. dist ((&n : real) / x))) -->
         ln (4 / pi))
        sequentially)``;
