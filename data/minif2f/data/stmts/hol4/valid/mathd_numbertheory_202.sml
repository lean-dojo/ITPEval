(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_202: the sum
  19^19 + 99^99 has remainder 8 modulo 10. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_202 =
  ``(((19 : num) EXP 19 + 99 EXP 99) MOD 10 = 8)``;
