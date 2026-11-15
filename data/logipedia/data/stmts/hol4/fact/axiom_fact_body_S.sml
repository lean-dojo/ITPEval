(*
  Statement-only formalization of the Logipedia corpus artifact
  fact.axiom_fact_body_S (catalog title "fact.axiom_fact_body_S"): for every
  natural number n, the module's abstract equality relation identifies
  fact_body at the successor of n with fact n multiplied by that successor.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_fact_fact",
  numSyntax.num --> numSyntax.num);

val _ = new_constant (
  "logipedia_fact_fact_body",
  numSyntax.num --> numSyntax.num);

val fact_axiom_fact_body_S =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_fact_fact_body (SUC n))
        (logipedia_fact_fact n * SUC n)``;
