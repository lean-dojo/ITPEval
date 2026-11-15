(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_709:
  divisor counts for 2*n and 3*n determine the divisor count for 6*n when n
  is a positive natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_709 =
  ``!n : num.
      0 < n /\
      CARD {k : num | divides k (2 * n)} = 28 /\
      CARD {k : num | divides k (3 * n)} = 30
      ==>
      CARD {k : num | divides k (6 * n)} = 35``;
