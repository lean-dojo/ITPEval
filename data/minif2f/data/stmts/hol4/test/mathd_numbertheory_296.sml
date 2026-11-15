(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_296: a natural
  number at least 2 that is both a perfect cube and a perfect fourth power is at least
  4096. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_296 =
  ``!n : num.
      2 <= n /\
      (?x : num. x ** 3 = n) /\
      (?t : num. t ** 4 = n)
      ==>
      4096 <= n``;
