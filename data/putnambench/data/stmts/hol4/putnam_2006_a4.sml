(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a4:
  the average number of endpoint-aware local maxima among permutations of
  n elements is (n + 1) / 3 for every n greater than one. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory real_sigmaTheory;

val putnam_2006_a4 =
  ``!n : num.
      1 < n
      ==>
      SIGMA
        (\p : num -> num.
           &(CARD
               {k : num |
                  k < n /\
                  (k = 0 \/ p (k - 1) < p k) /\
                  (k = n - 1 \/ p k > p (k + 1))}))
        {p : num -> num | p permutes count n} /
      &(CARD {p : num -> num | p permutes count n}) =
      (&(n + 1) : real) / 3``;
