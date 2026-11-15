(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1572 (catalog title "gcd.let_clause_1572"): for natural
  numbers m and n, positivity of n, a zero greatest common divisor, and
  zero-value assumptions for m and n imply that m is zero. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val gcd_let_clause_1572 =
  ``!m n : num.
      0 < n ==>
      gcd m n = 0 ==>
      m = 0 ==>
      n = 0 ==>
      m = 0``;
