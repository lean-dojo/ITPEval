(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_times_body_S (catalog title "nat.axiom_times_body_S"): for every
  natural number n, the source equality predicate relates times_body at the
  successor of n to the function mapping m to plus m (times n m). This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_binary_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_plus",
  logipedia_nat_binary_operator_type);

val _ = new_constant (
  "logipedia_nat_times",
  logipedia_nat_binary_operator_type);

val _ = new_constant (
  "logipedia_nat_times_body",
  logipedia_nat_binary_operator_type);

val nat_axiom_times_body_S =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_nat_times_body (SUC n))
        (\m : num.
          logipedia_nat_plus m (logipedia_nat_times n m))``;
