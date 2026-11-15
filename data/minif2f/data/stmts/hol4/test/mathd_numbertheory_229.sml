(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_229:
  the remainder of 5^30 modulo 7 is 1 for natural-number arithmetic. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_229 =
  ``((5 : num) EXP 30) MOD 7 = 1``;
