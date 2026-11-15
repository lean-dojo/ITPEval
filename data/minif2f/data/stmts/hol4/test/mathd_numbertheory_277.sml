(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_277:
  natural numbers with gcd 6 and lcm 126 have sum at least 60. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_277 =
  ``!m n : num.
      gcd m n = 6 /\
      lcm m n = 126
      ==>
      60 <= m + n``;
