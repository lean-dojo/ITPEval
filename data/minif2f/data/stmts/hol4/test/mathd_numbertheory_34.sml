(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_34:
  a natural number below 100 whose product with 9 is congruent to 1 modulo 100
  must equal 89. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_34 =
  ``!x : num.
      x < 100 /\
      (x * 9) MOD 100 = 1
      ==>
      x = 89``;
