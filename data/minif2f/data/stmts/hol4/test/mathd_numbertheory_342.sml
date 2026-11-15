(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_342:
  dividing 54 by 6 leaves remainder zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_342 =
  ``54 MOD 6 = 0``;
