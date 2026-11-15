(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_254:
  computing the remainder modulo 10 of the sum 239 + 174 + 83.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_254 =
  ``(239 + 174 + 83) MOD 10 = 6``;
