(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_92:
  a natural number whose product with 5 has remainder 8 modulo 17 has
  remainder 5 modulo 17. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_92 =
  ``!n : num.
      (5 * n) MOD 17 = 8
      ==>
      n MOD 17 = 5``;
