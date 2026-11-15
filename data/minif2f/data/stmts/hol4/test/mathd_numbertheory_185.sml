(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_185:
  a natural number congruent to 3 modulo 5 has twice its value congruent to 1
  modulo 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_185 =
  ``!n : num.
      n MOD 5 = 3
      ==>
      (2 * n) MOD 5 = 1``;
