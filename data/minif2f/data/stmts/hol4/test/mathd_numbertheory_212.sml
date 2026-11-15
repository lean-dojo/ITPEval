(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_212:
  evaluating the remainder modulo 10 of a product of three natural-number
  powers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_212 =
  ``((16 : num) EXP 17 * 17 EXP 18 * 18 EXP 19) MOD 10 = 8``;
