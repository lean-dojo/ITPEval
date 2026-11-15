(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b6:
  for every positive natural number n, the sum from 1 through n of the signs
  determined by the parity of floor(k * (sqrt 2 - 1)) is nonnegative. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory transcTheory;

val putnam_2020_b6 =
  ``!n : num.
      0 < n
      ==>
      0 <=
        SIGMA
          (\k : num.
             if (2 : int) int_divides
                  INT_FLOOR ((&k : real) * (sqrt 2 - 1))
             then (1 : real)
             else ~1)
          (IMAGE SUC (count n))``;
