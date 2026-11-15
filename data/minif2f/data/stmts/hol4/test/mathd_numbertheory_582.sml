(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_582:
  for a positive natural number divisible by 3, the sum of that number plus
  4, 6, and 8 is divisible by 9. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_582 =
  ``!n : num.
      0 < n /\
      divides 3 n
      ==>
      ((n + 4) + (n + 6) + (n + 8)) MOD 9 = 0``;
