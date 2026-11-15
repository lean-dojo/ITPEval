(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_188:
  the greatest common divisor of 180 and 168 is 12. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_188 =
  ``gcd 180 168 = 12``;
