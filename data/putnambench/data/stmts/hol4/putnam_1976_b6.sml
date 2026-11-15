(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b6:
  every natural number whose sum of positive natural divisors is one more
  than twice the number is the square of an odd natural number. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_1976_b6 =
  ``!N : num.
      SIGMA
        (\d : num. d)
        {d : num | 0 < d /\ d <= N /\ divides d N} =
      2 * N + 1
      ==>
      ?m : num. ODD m /\ m EXP 2 = N``;
