(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_gcd_r (catalog title "gcd.divides_gcd_r"): for all natural
  numbers n and m, their greatest common divisor divides m. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory;

val gcd_divides_gcd_r =
  ``!(n : num) (m : num). divides (gcd n m) m``;
