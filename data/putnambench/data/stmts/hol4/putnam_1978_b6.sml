(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b6:
  an upper bound for the square of a weighted double sum of real entries in
  the unit interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1978_b6 =
  ``!a : num -> num -> real. !m n : num.
      (!i j : num. 0 <= a i j /\ a i j <= 1) /\
      0 < m /\
      0 < n
      ==>
      (SIGMA
         (\i : num.
            SIGMA
              (\j : num. a i j / (&i : real))
              (IMAGE SUC (count (m * i))))
         (IMAGE SUC (count n))) pow 2 <=
      2 * (&m : real) *
      SIGMA
        (\i : num.
           SIGMA
             (\j : num. a i j)
             (IMAGE SUC (count (m * i))))
        (IMAGE SUC (count n))``;
