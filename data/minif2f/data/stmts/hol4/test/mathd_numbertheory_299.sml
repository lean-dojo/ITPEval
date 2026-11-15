(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_299:
  the product of the odd natural numbers from 1 through 13 has remainder 5
  modulo 10. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_299 =
  ``(1 * 3 * 5 * 7 * 9 * 11 * 13) MOD 10 = (5 : num)``;
