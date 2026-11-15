(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_335:
  multiplying a natural number congruent to 5 modulo 7 by 5 gives remainder
  4 modulo 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_335 =
  ``!n : num.
      n MOD 7 = 5 ==>
      (5 * n) MOD 7 = 4``;
