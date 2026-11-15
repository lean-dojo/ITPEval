(*
  Statement-only formalization of the Logipedia corpus artifact exp.eq_exp
  (catalog title "exp.eq_exp"): for all natural numbers n and m, Leibniz
  equality relates exp n m to filter_nat_type applied to the natural-number
  function exp_body n at m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_exp_operator_type =
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
  "logipedia_exp_exp",
  logipedia_exp_operator_type);

val _ = new_constant (
  "logipedia_exp_exp_body",
  logipedia_exp_operator_type);

val exp_eq_exp =
  ``!n m : num.
      logipedia_leibniz
        (logipedia_exp_exp n m)
        (logipedia_nat_filter_nat_type
           (logipedia_exp_exp_body n) m)``;
