(*
  Statement-only formalization of the Logipedia corpus artifact
  fact.axiom_fact (catalog title "fact.axiom_fact"): for every natural number
  n, the source equality predicate relates fact n to filter_nat_type applied
  to fact_body at n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_fact_fact",
  numSyntax.num --> numSyntax.num);

val _ = new_constant (
  "logipedia_fact_fact_body",
  numSyntax.num --> numSyntax.num);

val fact_axiom_fact =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_fact_fact n)
        (logipedia_nat_filter_nat_type
           logipedia_fact_fact_body n)``;
