(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_leb_body_S (catalog title "nat.axiom_leb_body_S"): for every
  natural number n, the source equality predicate relates leb_body at the
  successor of n to the Boolean function that is false at zero and returns
  leb n q at each successor q. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_leb_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  Type.bool;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_leb",
  logipedia_nat_leb_operator_type);

val _ = new_constant (
  "logipedia_nat_leb_body",
  logipedia_nat_leb_operator_type);

val logipedia_nat_match_nat_type_bool_def = new_definition (
  "logipedia_nat_match_nat_type_bool_def",
  ``logipedia_nat_match_nat_type_bool
      (zero_case : bool)
      (successor_case : num -> bool)
      (m : num) =
      COND (m = 0) zero_case (successor_case (PRE m))``);

val nat_axiom_leb_body_S =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_nat_leb_body (SUC n))
        (\m : num.
           logipedia_nat_match_nat_type_bool
             F
             (\q : num. logipedia_nat_leb n q)
             m)``;
