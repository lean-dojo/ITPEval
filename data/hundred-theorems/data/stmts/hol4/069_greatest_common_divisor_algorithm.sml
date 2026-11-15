(*
  Statement-only formalization of "Greatest Common Divisor Algorithm" from
  Hundred Theorems artifact 069. For all natural numbers, the algorithmic
  greatest common divisor divides both inputs, and every common divisor
  divides it. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory;

val greatest_common_divisor_algorithm =
  ``!a b : num.
      divides (gcd a b) a /\
      divides (gcd a b) b /\
      !e : num.
        divides e a /\ divides e b ==> divides e (gcd a b)``;
