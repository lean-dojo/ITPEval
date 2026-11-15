(*
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.eq_div_aux (catalog title "div_mod.eq_div_aux"): for every
  natural-number index, Leibniz equality relates div_aux at that index to
  filter_nat_type applied to div_aux_body at the same index, as curried binary
  functions on natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_div_mod_auxiliary_type =
  numSyntax.num -->
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
  "logipedia_div_mod_div_aux",
  logipedia_div_mod_auxiliary_type);

val _ = new_constant (
  "logipedia_div_mod_div_aux_body",
  logipedia_div_mod_auxiliary_type);

val div_mod_eq_div_aux =
  ``!p : num.
      logipedia_leibniz
        (logipedia_div_mod_div_aux p)
        (logipedia_nat_filter_nat_type
           logipedia_div_mod_div_aux_body p)``;
