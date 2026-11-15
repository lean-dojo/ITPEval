(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_247:
  a modular-arithmetic implication determining the remainder of a natural number
  modulo 11. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_247 =
  ``!n : num.
      (3 * n) MOD 11 = 2
      ==>
      n MOD 11 = 8``;
