(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_222:
  prescribed least common divisor and greatest common divisor with 120
  determine the natural number b. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_222 =
  ``!b : num.
      lcm 120 b = 3720 /\
      gcd 120 b = 8
      ==>
      b = 248``;
