(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_O (catalog title "gcd.axiom_gcd_aux_body_O"):
  at natural-number index zero, connectives.equal relates gcd_aux_body to the
  curried binary function that returns its first natural-number argument.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_gcd_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_gcd_gcd_aux_body",
  logipedia_gcd_auxiliary_type);

val gcd_axiom_gcd_aux_body_O =
  ``logipedia_connectives_equal
      (logipedia_gcd_gcd_aux_body 0)
      (\(m : num) (n : num). m)``;
