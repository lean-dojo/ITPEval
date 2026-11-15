(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_458:
  a natural number congruent to 7 modulo 8 is congruent to 3 modulo 4. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_458 =
  ``!n : num.
      n MOD 8 = 7
      ==>
      n MOD 4 = 3``;
