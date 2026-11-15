(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_235:
  evaluating the natural-number remainder modulo 10 of a sum of two products.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_235 =
  ``(29 * 79 + 31 * 81) MOD 10 = 2``;
