(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_eqb_body_O (catalog title "nat.eq_eqb_body_O"): Leibniz equality
  identifies eqb_body at natural-number zero with the Boolean function that
  is true at zero and false at every successor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_eqb_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  Type.bool;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_eqb_body",
  logipedia_nat_eqb_operator_type);

val nat_eq_eqb_body_O =
  ``logipedia_leibniz
      (logipedia_nat_eqb_body 0)
      (\m : num. m = 0)``;
