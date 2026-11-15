(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.eq_minus_gcd (catalog title "gcd.eq_minus_gcd"): for any two natural
  numbers, there are natural coefficients such that one of the two truncated
  product differences equals their greatest common divisor. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val gcd_eq_minus_gcd =
  ``!(m : num) (n : num).
      ?(a : num) (b : num).
        a * n - b * m = gcd n m \/
        b * m - a * n = gcd n m``;
