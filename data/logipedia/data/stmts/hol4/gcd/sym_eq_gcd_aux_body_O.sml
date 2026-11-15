(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_O (catalog title "gcd.sym_eq_gcd_aux_body_O"):
  Leibniz equality identifies the curried binary function returning its first
  natural-number argument with gcd_aux_body at natural-number index zero.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

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
  "logipedia_gcd_gcd_aux_body",
  logipedia_gcd_auxiliary_type);

val gcd_sym_eq_gcd_aux_body_O =
  ``logipedia_leibniz
      (\(m : num) (n : num). m)
      (logipedia_gcd_gcd_aux_body 0)``;
