(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_24:
  the sum of 11^k for natural exponents 1 through 9 has remainder 59 modulo
  100. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_24 =
  ``SIGMA
      (\k : num. 11 EXP k)
      (IMAGE SUC (count 9)) MOD 100 =
    59``;
