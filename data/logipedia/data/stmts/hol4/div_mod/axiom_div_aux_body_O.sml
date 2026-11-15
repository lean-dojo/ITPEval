(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_div_aux_body_O (catalog title
  "div_mod.axiom_div_aux_body_O"): at natural-number index zero,
  connectives.equal relates div_aux_body to the constant-zero curried binary
  function on natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_div_mod_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_div_mod_div_aux_body",
  logipedia_div_mod_auxiliary_type);

val div_mod_axiom_div_aux_body_O =
  ``logipedia_connectives_equal
      (logipedia_div_mod_div_aux_body 0)
      (\(m : num) (n : num). 0)``;
