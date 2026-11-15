(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_233:
  the canonical inverse of 24 modulo 11 squared is 116. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_233 =
  ``!b : num.
      b < 11 EXP 2 /\
      (b * 24) MOD (11 EXP 2) = 1
      ==>
      b = 116``;
