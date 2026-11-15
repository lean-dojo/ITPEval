(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_minus (catalog title "nat.sym_eq_minus"): for every natural
  number n, Leibniz equality relates filter_nat_type applied to minus_body at
  n to the natural-valued function minus n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_nat_minus_operator_type =
  numSyntax.num -->
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
  "logipedia_nat_minus",
  logipedia_nat_minus_operator_type);

val _ = new_constant (
  "logipedia_nat_minus_body",
  logipedia_nat_minus_operator_type);

val nat_sym_eq_minus =
  ``!n : num.
      logipedia_leibniz
        (logipedia_nat_filter_nat_type
           logipedia_nat_minus_body n)
        (logipedia_nat_minus n)``;
