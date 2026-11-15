(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_minus_body_S (catalog title "nat.sym_eq_minus_body_S"): for every
  natural number n, Leibniz equality relates the function that returns the
  successor of n at zero and minus n q at each successor q to minus_body at
  the successor of n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_minus_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

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
      if m = 0 then zero_case else successor_case (PRE m)``);

val nat_sym_eq_minus_body_S =
  ``!n : num.
      logipedia_leibniz
        (\m : num.
           logipedia_nat_match_nat_type_num
             (SUC n)
             (\q : num. logipedia_nat_minus n q)
             m)
        (logipedia_nat_minus_body (SUC n))``;
