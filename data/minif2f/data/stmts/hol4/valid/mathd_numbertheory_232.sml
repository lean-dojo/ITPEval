(*
  Statement-only formalization of miniF2F artifact mathd_numbertheory_232:
  canonical modular inverses of 3 and 5 modulo 31 force the inverse of their
  sum to be 29. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_232 =
  ``!x y z : num.
      x < 31 /\
      y < 31 /\
      z < 31 /\
      (x * 3) MOD 31 = 1 /\
      (y * 5) MOD 31 = 1 /\
      (z * (x + y)) MOD 31 = 1
      ==>
      z = 29``;
