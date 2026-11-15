(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1549 (catalog title "gcd.let_clause_1549"): if a natural
  number m is zero, then subtracting m leaves every natural number unchanged,
  under the stated positivity assumption on n. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val gcd_let_clause_1549 =
  ``!(m : num) (n : num).
      0 < n ==>
      0 = m ==>
      !x1106 : num.
        x1106 = x1106 - m``;
