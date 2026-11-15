(*
  Statement-only formalization of Logipedia corpus artifact div_mod.eq_div_O
  (catalog title "div_mod.eq_div_O"): for natural numbers n and m, if n is
  smaller than m, then the natural-number quotient of n by m is zero. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val div_mod_eq_div_O =
  ``!n m : num.
      n < m
      ==>
      n DIV m = 0``;
