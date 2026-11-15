(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_gcd_l (catalog title "gcd.divides_gcd_l"): for all natural
  numbers n and m, their greatest common divisor divides n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory;

val gcd_divides_gcd_l =
  ``!(n : num) (m : num). divides (gcd n m) n``;
