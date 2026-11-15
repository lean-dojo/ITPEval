(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_45:
  evaluating the greatest common divisor of 6432 and 132, then adding 11,
  gives 23. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_45 =
  ``gcd 6432 132 + 11 = 23``;
