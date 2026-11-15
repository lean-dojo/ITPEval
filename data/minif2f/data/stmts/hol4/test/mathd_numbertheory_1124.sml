(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_1124: a natural
  number at most 9 whose sum with 3740 is divisible by 18 must equal 4. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_1124 =
  ``!n : num.
      n <= 9 /\
      divides 18 (374 * 10 + n)
      ==>
      n = 4``;
