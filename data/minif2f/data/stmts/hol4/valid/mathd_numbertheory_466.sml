(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_466:
  the sum of the natural numbers below 11 has remainder 1 modulo 9. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_466 =
  ``(SIGMA (\k : num. k) (count 11)) MOD 9 = 1``;
