(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_257:
  a natural number between 1 and 100 is 45 when 77 divides the sum of the
  natural numbers from 0 through 100 after subtracting that number. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_257 =
  ``!x : num.
      (1 <= x /\ x <= 100) /\
      divides 77 (SIGMA (\k : num. k) (count 101) - x)
      ==>
      x = 45``;
