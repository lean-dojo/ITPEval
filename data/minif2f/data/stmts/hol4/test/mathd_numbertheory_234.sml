(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_234:
  a two-digit natural number with cube 912673 has digit sum 16. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_234 =
  ``!a b : num.
      (1 <= a /\ a <= 9 /\ b <= 9) /\
      ((10 * a + b) EXP 3 = 912673)
      ==>
      a + b = 16``;
