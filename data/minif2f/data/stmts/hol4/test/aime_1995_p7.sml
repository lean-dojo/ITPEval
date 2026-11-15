(*
  Statement-only formalization of miniF2F test problem aime_1995_p7: trigonometric equations
  determining positive coprime natural numbers whose sum is 27. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory realTheory transcTheory;

val aime_1995_p7 =
  ``!k : num. !m : num. !n : num. !t : real.
      0 < k /\ 0 < m /\ 0 < n /\
      gcd m n = 1 /\
      (1 + sin t) * (1 + cos t) = 5 / 4 /\
      (1 - sin t) * (1 - cos t) = &m / &n - sqrt (&k)
      ==>
      k + m + n = 27``;
