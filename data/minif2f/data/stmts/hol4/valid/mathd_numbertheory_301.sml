(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_301:
  for every positive natural number j, 3 * (7 * j + 3) has remainder 2 modulo
  7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_301 =
  ``!j : num.
      0 < j
      ==>
      (3 * (7 * j + 3)) MOD 7 = 2``;
