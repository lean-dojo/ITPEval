(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.axiom_gcd_aux (catalog title "gcd.axiom_gcd_aux"): for every
  natural-number index, the source equality predicate relates gcd_aux at that
  index to filter_nat_type applied to gcd_aux_body at the same index, as
  curried binary functions on natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_gcd_auxiliary_type =
  numSyntax.num -->
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
  "logipedia_gcd_gcd_aux",
  logipedia_gcd_auxiliary_type);

val _ = new_constant (
  "logipedia_gcd_gcd_aux_body",
  logipedia_gcd_auxiliary_type);

val gcd_axiom_gcd_aux =
  ``!p : num.
      logipedia_connectives_equal
        (logipedia_gcd_gcd_aux p)
        (logipedia_nat_filter_nat_type
           logipedia_gcd_gcd_aux_body p)``;
