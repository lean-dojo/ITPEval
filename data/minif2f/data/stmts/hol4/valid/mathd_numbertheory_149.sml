(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_149:
  the sum of natural numbers below 50 that are congruent to 5 modulo 8 and to
  3 modulo 6 is 66. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_149 =
  ``SIGMA
      (\k : num. k)
      {x : num | x < 50 /\ x MOD 8 = 5 /\ x MOD 6 = 3} =
    66``;
