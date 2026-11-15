(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_33:
  a natural number below 398 whose product with 7 has remainder 1 modulo 398
  equals 57. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_33 =
  ``!n : num.
      (n < 398 /\ (n * 7) MOD 398 = 1)
      ==>
      n = 57``;
