(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_66:
  computing the natural-number remainder of 194 upon division by 11.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_66 =
  ``(194 : num) MOD 11 = 7``;
