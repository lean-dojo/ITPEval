(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_495:
  positive natural numbers ending in 2 and 4 with gcd 6 have lcm at least 108.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_495 =
  ``!a b : num.
      0 < a /\
      0 < b /\
      a MOD 10 = 2 /\
      b MOD 10 = 4 /\
      gcd a b = 6
      ==>
      108 <= lcm a b``;
