(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_99:
  solving a natural-number congruence modulo 47 after multiplication by 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_99 =
  ``!n : num.
      (2 * n) MOD 47 = 15
      ==>
      n MOD 47 = 31``;
