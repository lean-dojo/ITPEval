(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_640:
  the sum of four specified consecutive natural numbers has remainder 2
  modulo 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_640 =
  ``((91145 + 91146 + 91147 + 91148 : num) MOD 4 = 2)``;
