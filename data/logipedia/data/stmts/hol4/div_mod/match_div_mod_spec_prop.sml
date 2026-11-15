(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.match_div_mod_spec_prop (catalog title
  "div_mod.match_div_mod_spec_prop"): the abstract natural-number division
  specification may be eliminated by supplying a continuation that accepts
  a bounded remainder and the equation n = q * m + r. This file contains no
  proof.
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

val div_mod_match_div_mod_spec_prop =
  ``!(n : num) (m : num) (q : num) (r : num) (return_ : bool).
      (r < m ==> n = q * m + r ==> return_) ==>
      logipedia_div_mod_spec n m q r ==>
      return_``;
