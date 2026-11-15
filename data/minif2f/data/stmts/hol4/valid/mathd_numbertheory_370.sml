(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_370:
  a natural number congruent to 3 modulo 7 makes twice that number plus 1
  divisible by 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_370 =
  ``!n : num.
      n MOD 7 = 3 ==>
      (2 * n + 1) MOD 7 = 0``;
