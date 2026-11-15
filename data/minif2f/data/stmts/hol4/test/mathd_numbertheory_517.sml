(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_517:
  the product 121 * 122 * 123 has remainder 2 modulo 4 in the natural numbers.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_517 =
  ``((121 : num) * 122 * 123) MOD 4 = 2``;
