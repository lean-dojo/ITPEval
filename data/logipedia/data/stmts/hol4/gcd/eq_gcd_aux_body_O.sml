(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.eq_gcd_aux_body_O (catalog title "gcd.eq_gcd_aux_body_O"): Leibniz
  equality identifies gcd_aux_body at natural-number index zero with the
  curried binary function that returns its first natural-number argument.
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

val gcd_eq_gcd_aux_body_O =
  ``logipedia_leibniz
      (logipedia_gcd_gcd_aux_body 0)
      (\(m : num) (n : num). m)``;
