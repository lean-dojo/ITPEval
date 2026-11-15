(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_559:
  congruence conditions on two natural numbers modulo 3, 5, and 10 imply that
  the first number is at least 14. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_559 =
  ``!x y : num.
      x MOD 3 = 2 /\
      y MOD 5 = 4 /\
      x MOD 10 = y MOD 10
      ==>
      14 <= x``;
