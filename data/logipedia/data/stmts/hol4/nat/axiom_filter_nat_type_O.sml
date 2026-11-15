(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_filter_nat_type_O (catalog title
  "nat.axiom_filter_nat_type_O"): for every result type and function on
  natural numbers, the source equality predicate relates filter_nat_type
  applied at zero to the function's value at zero. This file contains no
  proof.
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

val nat_axiom_filter_nat_type_O =
  ``!return_ : num -> 'a.
      logipedia_connectives_equal
        (logipedia_nat_filter_nat_type return_ 0)
        (return_ 0)``;
