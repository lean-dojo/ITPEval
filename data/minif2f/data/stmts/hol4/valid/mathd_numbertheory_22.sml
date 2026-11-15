(*
  Statement-only formalization of miniF2F valid artifact mathd_numbertheory_22:
  a natural number below 10 for which 10*b+6 is a perfect square must be 3 or 1.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_22 =
  ``!b : num.
      b < 10 /\ (?a : num. 10 * b + 6 = a * a)
      ==>
      (b = 3 \/ b = 1)``;
