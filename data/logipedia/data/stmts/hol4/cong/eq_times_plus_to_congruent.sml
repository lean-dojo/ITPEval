(*
  Statement-only formalization of Logipedia corpus artifact
  cong.eq_times_plus_to_congruent (catalog title
  "cong.eq_times_plus_to_congruent"): for natural numbers and a positive
  modulus p, an equality n = r * p + m implies that n and m are congruent
  modulo p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val cong_eq_times_plus_to_congruent =
  ``!n m p r : num.
      0 < p ==>
      n = r * p + m ==>
      logipedia_cong_congruent n m p``;
