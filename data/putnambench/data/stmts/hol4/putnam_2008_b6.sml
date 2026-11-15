(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b6:
  the number of permutations with every displacement bounded by k is odd
  exactly when n is congruent to zero or one modulo 2k+1. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory;

val putnam_2008_b6 =
  ``!n k : num.
      0 < n /\ 0 < k
      ==>
      (ODD
         (CARD
            {p : num -> num |
               p permutes count n /\
               !i : num.
                 i < n
                 ==>
                 p i <= i + k /\ i <= p i + k}) =
       (n MOD (2 * k + 1) = 0 \/
        n MOD (2 * k + 1) = 1))``;
