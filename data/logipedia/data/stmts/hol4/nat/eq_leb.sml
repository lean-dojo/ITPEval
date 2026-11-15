(*
  Statement-only formalization of the Logipedia corpus artifact nat.eq_leb
  (catalog title "nat.eq_leb"): for every natural number n, Leibniz equality
  relates the Boolean-valued function leb n to filter_nat_type applied to
  leb_body at n. This file contains no proof.
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

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_nat_leb",
  logipedia_nat_leb_operator_type);

val _ = new_constant (
  "logipedia_nat_leb_body",
  logipedia_nat_leb_operator_type);

val nat_eq_leb =
  ``!n : num.
      logipedia_leibniz
        (logipedia_nat_leb n)
        (logipedia_nat_filter_nat_type
           logipedia_nat_leb_body n)``;
