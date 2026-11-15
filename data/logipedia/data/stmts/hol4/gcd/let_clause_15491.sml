(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_15491 (catalog title "gcd.let_clause_15491"): for arbitrary
  natural numbers m and n, if n is zero, then every natural x1106 equals
  x1106 minus n. The parameter m does not occur in the conclusion. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val gcd_let_clause_15491 =
  ``!(m : num) (n : num).
      0 = n
      ==>
      !x1106 : num.
        x1106 = x1106 - n``;
