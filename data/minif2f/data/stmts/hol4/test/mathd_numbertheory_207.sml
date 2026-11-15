(*
  Statement-only formalization of miniF2F artifact mathd_numbertheory_207:
  evaluation of the natural-number expression 8 * 9^2 + 5 * 9 + 2 as 695.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_207 =
  ``(8 : num) * (9 EXP 2) + 5 * 9 + 2 = 695``;
