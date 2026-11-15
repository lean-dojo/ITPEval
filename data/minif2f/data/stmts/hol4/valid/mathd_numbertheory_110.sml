(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_110:
  natural-number congruences modulo 10 determining a difference. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_110 =
  ``!a b : num.
      0 < a /\ 0 < b /\ b <= a /\
      (a + b) MOD 10 = 2 /\
      (2 * a + b) MOD 10 = 1
      ==>
      (a - b) MOD 10 = 6``;
