(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_156:
  bounding by 13 the greatest common divisor of n + 7 and 2 * n + 1 for every
  positive natural number n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_156 =
  ``!n : num.
      0 < n
      ==>
      gcd (n + 7) (2 * n + 1) <= 13``;
