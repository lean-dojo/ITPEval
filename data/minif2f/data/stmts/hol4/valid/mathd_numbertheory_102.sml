(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_102: evaluating a
  modular exponentiation of natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_102 =
  ``((2 : num) EXP 8) MOD 5 = 1``;
