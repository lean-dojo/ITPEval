(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_447:
  summing the last decimal digits of the multiples of 3 from 1 through 49.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_447 =
  ``SIGMA (\k : num. k MOD 10)
      {k : num | 1 <= k /\ k <= 49 /\ divides 3 k} = 78``;
