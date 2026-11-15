(*
  Statement-only formalization of Logipedia corpus artifact div_mod.mod_O_n
  (catalog title "div_mod.mod_O_n"): for every natural number n, the
  remainder of zero upon division by n is zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val div_mod_mod_O_n =
  ``!n : num. 0 MOD n = 0``;
