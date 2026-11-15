(*
  Statement-only formalization of the Logipedia corpus artifact nat.eq_plus
  (catalog title "nat.eq_plus"): for every natural number n, Leibniz equality
  relates the natural-valued function plus n to filter_nat_type applied to
  plus_body at n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_nat_plus_operator_type =
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
  "logipedia_nat_plus",
  logipedia_nat_plus_operator_type);

val _ = new_constant (
  "logipedia_nat_plus_body",
  logipedia_nat_plus_operator_type);

val nat_eq_plus =
  ``!n : num.
      logipedia_leibniz
        (logipedia_nat_plus n)
        (logipedia_nat_filter_nat_type
           logipedia_nat_plus_body n)``;
