(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_mod_spec_intro (catalog title "div_mod.div_mod_spec_intro"):
  for all natural numbers n, m, q, and r, a remainder smaller than m and the
  decomposition n = q * m + r entail the abstract division-specification
  predicate for n, m, q, and r. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_constant (
  "logipedia_div_mod_spec",
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  Type.bool);

val div_mod_div_mod_spec_intro =
  ``!n m q r : num.
      r < m ==>
      n = q * m + r ==>
      logipedia_div_mod_spec n m q r``;
