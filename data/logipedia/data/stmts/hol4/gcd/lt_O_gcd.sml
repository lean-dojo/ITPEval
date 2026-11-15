(*
  Statement-only formalization of the Logipedia corpus artifact gcd.lt_O_gcd
  (catalog title "gcd.lt_O_gcd"): for natural numbers m and n, if n is
  positive, then their greatest common divisor is positive. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val gcd_lt_O_gcd =
  ``!(m : num) (n : num). 0 < n ==> 0 < gcd m n``;
