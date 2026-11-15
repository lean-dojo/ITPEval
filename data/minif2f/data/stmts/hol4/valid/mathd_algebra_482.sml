(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_482: distinct natural
  primes that are roots of the real quadratic x^2 - 12*x + k force k = 35. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory realTheory;

val mathd_algebra_482 =
  ``!m n : num. !k : real. !f : real -> real.
      prime m /\
      prime n /\
      (!x : real. f x = x pow 2 - 12 * x + k) /\
      f (&m) = 0 /\
      f (&n) = 0 /\
      ~(m = n)
      ==>
      k = 35``;
