(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_618:
  a nontrivial gcd of consecutive values of x^2 - x + 41 at a positive natural
  input implies that the input is at least 41. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_618 =
  ``!n : num. !p : num -> num.
      0 < n /\
      (!x : num. p x = x ** 2 - x + 41) /\
      1 < gcd (p n) (p (n + 1))
      ==>
      41 <= n``;
