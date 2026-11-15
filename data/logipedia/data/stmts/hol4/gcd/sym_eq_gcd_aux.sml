(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.sym_eq_gcd_aux (catalog title "gcd.sym_eq_gcd_aux"): for every
  natural-number index p, Leibniz equality identifies filter_nat_type applied
  to gcd_aux_body at p with gcd_aux p, as curried binary natural-number
  functions. This file contains no proof.
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

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_gcd_gcd_aux",
  logipedia_gcd_auxiliary_type);

val _ = new_constant (
  "logipedia_gcd_gcd_aux_body",
  logipedia_gcd_auxiliary_type);

val gcd_sym_eq_gcd_aux =
  ``!p : num.
      logipedia_leibniz
        (logipedia_nat_filter_nat_type
           logipedia_gcd_gcd_aux_body p)
        (logipedia_gcd_gcd_aux p)``;
