(*
  Statement-only formalization of the Logipedia corpus artifact
  permutation.sym_eq_invert_permut (catalog title
  "permutation.sym_eq_invert_permut"): for every natural number n, Leibniz
  equality relates filter_nat_type applied to invert_permut_body at n to
  invert_permut n. This file contains no proof.
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

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut",
  logipedia_permutation_invert_permut_type);

val _ = new_constant (
  "logipedia_permutation_invert_permut_body",
  logipedia_permutation_invert_permut_type);

val permutation_sym_eq_invert_permut =
  ``!n : num.
      logipedia_leibniz
        (logipedia_nat_filter_nat_type
           logipedia_permutation_invert_permut_body n)
        (logipedia_permutation_invert_permut n)``;
