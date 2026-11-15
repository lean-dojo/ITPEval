(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.commutative_gcd (catalog title "gcd.commutative_gcd"): the greatest
  common divisor of two natural numbers is unchanged when the arguments are
  exchanged. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val gcd_commutative_gcd =
  ``!(n : num) (m : num). gcd n m = gcd m n``;
