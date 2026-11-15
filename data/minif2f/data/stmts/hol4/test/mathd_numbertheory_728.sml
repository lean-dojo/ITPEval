(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_728:
  the difference 29^13 - 5^13 has remainder 3 modulo 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_728 =
  ``(29 EXP 13 - 5 EXP 13) MOD 7 = (3 : num)``;
