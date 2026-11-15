(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a6:
  a finite collection of points in the real unit interval admits another
  point whose reciprocal-distance sum satisfies the stated harmonic bound.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1979_a6 =
  ``!n : num. !p : num -> real.
      (!i : num.
         i IN count n
         ==>
         0 <= p i /\ p i <= 1)
      ==>
      ?x : real.
        0 <= x /\ x <= 1 /\
        (!i : num. i IN count n ==> x <> p i) /\
        SIGMA
          (\i : num. 1 / abs (x - p i))
          (count n) <=
        8 * (&n : real) *
          SIGMA
            (\i : num. (1 : real) / (2 * (&i : real) + 1))
            (count n)``;
