(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_711:
  positive natural numbers with greatest common divisor 8 and least common
  multiple 112 have sum at least 72. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_711 =
  ``!m n : num.
      0 < m /\
      0 < n /\
      gcd m n = 8 /\
      lcm m n = 112
      ==>
      72 <= m + n``;
