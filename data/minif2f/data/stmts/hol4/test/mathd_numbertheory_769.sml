(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_769:
  the sum of 129^34 and 96^38 has remainder 9 modulo 11. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_769 =
  ``(129 EXP 34 + 96 EXP 38) MOD 11 = (9 : num)``;
