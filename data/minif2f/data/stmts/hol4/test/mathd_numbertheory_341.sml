(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_341: the last
  three decimal digits of 5^100 have digit sum 13. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_341 =
  ``!a b c : num.
      (a <= 9 /\ b <= 9 /\ c <= 9) /\
      ((5 EXP 100) MOD 1000 = 10 * (10 * a + b) + c)
      ==>
      a + b + c = 13``;
