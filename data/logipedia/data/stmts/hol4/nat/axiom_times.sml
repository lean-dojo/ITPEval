(*
  Statement-only formalization of the Logipedia corpus artifact nat.axiom_times
  (catalog title "nat.axiom_times"): for every natural number n, the source
  equality predicate relates the natural-valued function times n to
  filter_nat_type applied to times_body at n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_nat_times_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_nat_times",
  logipedia_nat_times_operator_type);

val _ = new_constant (
  "logipedia_nat_times_body",
  logipedia_nat_times_operator_type);

val nat_axiom_times =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_nat_times n)
        (logipedia_nat_filter_nat_type
           logipedia_nat_times_body n)``;
