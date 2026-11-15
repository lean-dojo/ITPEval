(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_198: the remainder
  of 5^2005 modulo 100 is 25. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_198 =
  ``((5 : num) EXP 2005) MOD 100 = 25``;
