(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_minus_body_S (catalog title "nat.axiom_minus_body_S"): for every
  natural number n, the source equality predicate relates minus_body at the
  successor of n to the function that returns that successor at zero and
  minus n q at each successor q. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_minus_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_minus",
  logipedia_nat_minus_operator_type);

val _ = new_constant (
  "logipedia_nat_minus_body",
  logipedia_nat_minus_operator_type);

val logipedia_nat_match_nat_type_num_def = new_definition (
  "logipedia_nat_match_nat_type_num_def",
  ``logipedia_nat_match_nat_type_num
      (zero_case : num)
      (successor_case : num -> num)
      (m : num) =
      COND (m = 0) zero_case (successor_case (PRE m))``);

val nat_axiom_minus_body_S =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_nat_minus_body (SUC n))
        (\m : num.
           logipedia_nat_match_nat_type_num
             (SUC n)
             (\q : num. logipedia_nat_minus n q)
             m)``;
