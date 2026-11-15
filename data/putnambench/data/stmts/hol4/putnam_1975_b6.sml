(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b6:
  the harmonic partial sums satisfy two strict inequalities involving
  positive real powers for every natural number above the stated bounds.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_1975_b6 =
  ``let s =
      \n : num.
        SIGMA
          (\i : num. (1 : real) / &i)
          (IMAGE SUC (count n))
    in
      (!n : num.
         1 < n
         ==>
         (&n : real) * ((&(n + 1) : real) powr (1 / (&n : real))) <
           (&n : real) + s n) /\
      (!n : num.
         2 < n
         ==>
         ((&n : real) - 1) *
             ((&n : real) powr (-1 / ((&n : real) - 1))) <
           (&n : real) - s n)``;
