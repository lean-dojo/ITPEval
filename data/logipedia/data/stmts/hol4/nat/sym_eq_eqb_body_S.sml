(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_eqb_body_S (catalog title "nat.sym_eq_eqb_body_S"): for every
  natural number n, Leibniz equality identifies the Boolean function that is
  false at zero and returns eqb n q at each successor q with eqb_body at the
  successor of n. This file contains no proof.
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
  "logipedia_nat_eqb",
  logipedia_nat_eqb_operator_type);

val _ = new_constant (
  "logipedia_nat_eqb_body",
  logipedia_nat_eqb_operator_type);

val logipedia_nat_match_nat_type_bool_def = new_definition (
  "logipedia_nat_match_nat_type_bool_def",
  ``logipedia_nat_match_nat_type_bool
      (zero_case : bool)
      (successor_case : num -> bool)
      (m : num) =
      if m = 0 then zero_case else successor_case (PRE m)``);

val nat_sym_eq_eqb_body_S =
  ``!n : num.
      logipedia_leibniz
        (\m : num.
           logipedia_nat_match_nat_type_bool
             F
             (\q : num. logipedia_nat_eqb n q)
             m)
        (logipedia_nat_eqb_body (SUC n))``;
