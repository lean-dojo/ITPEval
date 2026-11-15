(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_div_mod_spec (catalog title
  "primes.divides_to_div_mod_spec"): for natural numbers n and m, if n is
  positive and divides m, then m has quotient m DIV n and remainder zero in
  the natural-number division specification. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_div_mod_spec_def = new_definition (
  "logipedia_div_mod_spec_def",
  ``logipedia_div_mod_spec
      (a : num) (b : num) (q : num) (r : num) <=>
      r < b /\ a = q * b + r``);

val primes_divides_to_div_mod_spec =
  ``!(n : num) (m : num).
      0 < n ==>
      divides n m ==>
      logipedia_div_mod_spec m n (m DIV n) 0``;
