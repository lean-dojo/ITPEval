(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1571 (catalog title "gcd.let_clause_1571"): for natural
  numbers m and n, positivity of n together with zero gcd and zero-value
  assumptions for m and n imply that m equals n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val gcd_let_clause_1571 =
  ``!m n : num.
      0 < n ==>
      gcd m n = 0 ==>
      m = 0 ==>
      n = 0 ==>
      m = n``;
