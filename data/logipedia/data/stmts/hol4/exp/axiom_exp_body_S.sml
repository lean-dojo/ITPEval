(*
  Statement-only formalization of the Logipedia corpus artifact
  exp.axiom_exp_body_S (catalog title "exp.axiom_exp_body_S"): for all natural
  numbers n and m, the source equality relation identifies exp_body n at the
  successor of m with exp n m multiplied by n. This file contains no proof.
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
  "logipedia_exp_exp",
  logipedia_exp_operator_type);

val _ = new_constant (
  "logipedia_exp_exp_body",
  logipedia_exp_operator_type);

val exp_axiom_exp_body_S =
  ``!n m : num.
      logipedia_connectives_equal
        (logipedia_exp_exp_body n (SUC m))
        (logipedia_exp_exp n m * n)``;
