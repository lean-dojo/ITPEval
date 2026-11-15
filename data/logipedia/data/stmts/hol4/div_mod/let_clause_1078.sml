(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.let_clause_1078 (catalog title "div_mod.let_clause_1078"): two
  natural-number division specifications and their explicit decompositions,
  together with non-strict and strict quotient-order hypotheses, imply the
  reordered first decomposition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_div_mod_spec_def = new_definition (
  "logipedia_div_mod_spec_def",
  ``logipedia_div_mod_spec
      (a : num) (b : num) (q : num) (r : num) <=>
      r < b /\ a = q * b + r``);

val div_mod_let_clause_1078 =
  ``!a b q r q1 r1 : num.
      logipedia_div_mod_spec a b q r ==>
      r < b ==>
      a = q * b + r ==>
      logipedia_div_mod_spec a b q1 r1 ==>
      r1 < b ==>
      a = q1 * b + r1 ==>
      q <= q1 ==>
      q < q1 ==>
      a = r + b * q``;
