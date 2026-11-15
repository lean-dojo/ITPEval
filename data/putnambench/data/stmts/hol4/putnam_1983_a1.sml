(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_a1:
  the number of positive integers dividing at least one of 10^40 and 20^30
  is 2301. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_1983_a1 =
  ``CARD
      {n : num |
         0 < n /\
         (divides n (10 EXP 40) \/ divides n (20 EXP 30))} =
    2301``;
