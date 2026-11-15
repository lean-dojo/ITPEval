(*
  Statement-only formalization of Logipedia corpus artifact div_mod.div_times
  (catalog title "div_mod.div_times"): for natural numbers a and positive b,
  dividing a * b by b returns a. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val div_mod_div_times =
  ``!a b : num.
      0 < b
      ==>
      (a * b) DIV b = a``;
