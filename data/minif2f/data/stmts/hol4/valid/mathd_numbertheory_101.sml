(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_101: evaluating the
  remainder of a product of natural numbers modulo 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_101 =
  ``((17 : num) * 18) MOD 4 = 2``;
