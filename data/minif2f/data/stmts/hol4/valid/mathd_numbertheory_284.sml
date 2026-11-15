(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_284:
  bounded natural-number digits satisfying that their two-digit numeral is
  twice their sum yield the numeral 18. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_284 =
  ``!a b : num.
      (1 <= a /\ a <= 9 /\ b <= 9) /\
      (10 * a + b = 2 * (a + b))
      ==>
      10 * a + b = 18``;
