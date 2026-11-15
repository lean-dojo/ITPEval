(*
  Statement-only formalization of the Logipedia corpus artifact gcd.gcd_O_l
  (catalog title "gcd.gcd_O_l"): zero is a left identity for the greatest
  common divisor on natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val gcd_gcd_O_l =
  ``!m : num. gcd 0 m = m``;
