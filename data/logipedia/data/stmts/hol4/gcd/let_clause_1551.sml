(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1551 (catalog title "gcd.let_clause_1551"): for arbitrary
  natural numbers m and n, if n is zero, then multiplying n by any natural
  number x347 still yields n. The parameter m is unused. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val gcd_let_clause_1551 =
  ``!(m : num) (n : num).
      0 = n
      ==>
      !x347 : num.
        n = x347 * n``;
