(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_169:
  the greatest common divisor of 20 factorial and 200000 is 40000. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_169 =
  ``gcd (FACT 20) 200000 = 40000``;
