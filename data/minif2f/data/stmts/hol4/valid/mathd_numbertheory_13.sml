(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_13: the two positive
  natural numbers in the specified intervals whose products by 14 have remainder 46 modulo 100
  have average 64. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_13 =
  ``!u v : num.
      0 < u /\
      0 < v /\
      (14 * u) MOD 100 = 46 /\
      (14 * v) MOD 100 = 46 /\
      u < 50 /\
      50 < v /\
      v < 100
      ==>
      (u + v) DIV 2 = 64``;
