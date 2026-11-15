(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_30:
  the sum of the squares of 33818 through 33822 is divisible by 17. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_30 =
  ``(33818 EXP 2 + 33819 EXP 2 + 33820 EXP 2 +
      33821 EXP 2 + 33822 EXP 2) MOD 17 = 0``;
