(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_200:
  the remainder of 139 modulo 11 is 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_200 =
  ``((139 : num) MOD 11 = 7)``;
