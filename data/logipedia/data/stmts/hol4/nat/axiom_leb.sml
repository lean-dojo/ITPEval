(*
  Statement-only formalization of the Logipedia corpus artifact nat.axiom_leb
  (catalog title "nat.axiom_leb"): for every natural number n, the source
  equality predicate relates the Boolean-valued function leb n to
  filter_nat_type applied to leb_body at n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_nat_leb_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  Type.bool;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_nat_leb",
  logipedia_nat_leb_operator_type);

val _ = new_constant (
  "logipedia_nat_leb_body",
  logipedia_nat_leb_operator_type);

val nat_axiom_leb =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_nat_leb n)
        (logipedia_nat_filter_nat_type
           logipedia_nat_leb_body n)``;
