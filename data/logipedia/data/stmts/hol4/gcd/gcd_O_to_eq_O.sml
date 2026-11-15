(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.gcd_O_to_eq_O (catalog title "gcd.gcd_O_to_eq_O"): if the greatest
  common divisor of two natural numbers is zero, then both numbers are zero.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val gcd_gcd_O_to_eq_O =
  ``!(m : num) (n : num).
      gcd m n = 0 ==> (m = 0 /\ n = 0)``;
