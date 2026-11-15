(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_328:
  the remainder of 5 raised to the power 999999 upon division by 7 is 6.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_328 =
  ``(5 EXP 999999) MOD 7 = (6 : num)``;
