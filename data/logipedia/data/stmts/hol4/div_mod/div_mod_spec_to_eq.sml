(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_mod_spec_to_eq (catalog title
  "div_mod.div_mod_spec_to_eq"): two natural-number division specifications
  for the same dividend and divisor have equal quotients. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_div_mod_spec_def = new_definition (
  "logipedia_div_mod_spec_def",
  ``logipedia_div_mod_spec
      (a : num) (b : num) (q : num) (r : num) <=>
      r < b /\ a = q * b + r``);

val div_mod_div_mod_spec_to_eq =
  ``!a b q r q1 r1 : num.
      logipedia_div_mod_spec a b q r ==>
      logipedia_div_mod_spec a b q1 r1 ==>
      q = q1``;
