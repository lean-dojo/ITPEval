(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_211:
  counting the natural numbers below 60 for which the integer 4*n - 2 is
  divisible by 6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val mathd_numbertheory_211 =
  ``CARD {n : num |
      n < 60 /\
      (6 : int) int_divides (4 * int_of_num n - 2)} = 20``;
