(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_321:
  the canonical residue inverse of 160 modulo 1399 is 1058. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_321 =
  ``!n : num.
      n < 1399 /\
      (n * 160) MOD 1399 = 1
      ==>
      n = 1058``;
