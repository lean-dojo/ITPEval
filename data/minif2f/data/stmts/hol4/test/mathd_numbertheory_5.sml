(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_5:
  a natural number at least 10 that is both a perfect square and a perfect cube
  is at least 64. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_5 =
  ``!n : num.
      10 <= n /\
      (?x : num. x ** 2 = n) /\
      (?t : num. t ** 3 = n)
      ==>
      64 <= n``;
