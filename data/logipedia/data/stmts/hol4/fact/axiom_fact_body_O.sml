(*
  Statement-only formalization of the Logipedia corpus artifact
  fact.axiom_fact_body_O (catalog title "fact.axiom_fact_body_O"): at
  natural-number zero, the module's abstract equality relation identifies
  fact_body zero with the successor of zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_fact_fact_body",
  numSyntax.num --> numSyntax.num);

val fact_axiom_fact_body_O =
  ``logipedia_connectives_equal
      (logipedia_fact_fact_body 0)
      (SUC 0)``;
