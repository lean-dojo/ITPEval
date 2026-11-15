(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.axiom_invert_permut (catalog title
  "permutation.axiom_invert_permut"): for every natural number n, the source
  equality predicate relates invert_permut n to filter_nat_type applied to
  invert_permut_body at n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_permutation_invert_permut_type =
  numSyntax.num -->
  (numSyntax.num --> numSyntax.num) -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut",
  logipedia_permutation_invert_permut_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut_body",
  logipedia_permutation_invert_permut_type);

val permutation_axiom_invert_permut =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_permutation_invert_permut n)
        (logipedia_nat_filter_nat_type
           logipedia_permutation_invert_permut_body n)``;
