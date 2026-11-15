(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.prime_to_gcd_1 (catalog title "gcd.prime_to_gcd_1"): for natural
  numbers n and m, if n is prime and does not divide m, then their greatest
  common divisor is one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory;

val gcd_prime_to_gcd_1 =
  ``!(n : num) (m : num).
      prime n ==>
      ~divides n m ==>
      gcd n m = 1``;
