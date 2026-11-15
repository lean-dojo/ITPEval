(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_42:
  two natural-number solutions of 27 * n = 17 modulo 40 in consecutive
  residue intervals have sum 62. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_42 =
  ``!u v : num.
      (27 * u) MOD 40 = 17 /\
      (27 * v) MOD 40 = 17 /\
      u < 40 /\
      v < 80 /\
      40 < v
      ==>
      u + v = 62``;
