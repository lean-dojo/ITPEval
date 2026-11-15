(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_48:
  the positive natural-number solution of 3 * b^2 + 2 * b + 1 = 57 is 4.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_48 =
  ``!b : num.
      0 < b /\
      3 * b EXP 2 + 2 * b + 1 = 57
      ==>
      b = 4``;
