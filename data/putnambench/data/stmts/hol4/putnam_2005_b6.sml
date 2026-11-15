(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b6:
  the signed sum over permutations of n elements, weighted by one plus each
  permutation's number of fixed points. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory real_sigmaTheory;

val putnam_2005_b6 =
  ``!n : num.
      0 < n
      ==>
      SIGMA
        (\p : num -> num.
           (if evenperm p then (1 : real) else ~(1 : real)) /
           (&(CARD {i : num | i < n /\ p i = i}) + 1))
        {p : num -> num | p permutes count n} =
      (-1 : real) pow (n + 1) * (&n : real) / &(n + 1)``;
