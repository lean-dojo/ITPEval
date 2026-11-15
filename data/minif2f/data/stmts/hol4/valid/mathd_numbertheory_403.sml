(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_403:
  the natural-number proper divisors of 198 sum to 270. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_403 =
  ``SIGMA
      (\k : num. k)
      {k : num | divides k 198 /\ ~(k = 198)} =
    270``;
