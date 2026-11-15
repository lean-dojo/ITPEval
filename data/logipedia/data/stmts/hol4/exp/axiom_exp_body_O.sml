(*
  Statement-only formalization of the Logipedia corpus artifact
  exp.axiom_exp_body_O (catalog title "exp.axiom_exp_body_O"): for every
  natural number n, the module's abstract equality relation identifies
  exp_body n at zero with the successor of zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_exp_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_exp_exp_body",
  logipedia_exp_operator_type);

val exp_axiom_exp_body_O =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_exp_exp_body n 0)
        (SUC 0)``;
