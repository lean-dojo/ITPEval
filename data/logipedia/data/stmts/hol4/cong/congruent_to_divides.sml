(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_to_divides (catalog title "cong.congruent_to_divides"):
  for natural numbers, congruence modulo a positive modulus implies that the
  modulus divides their truncated natural-number difference. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val cong_congruent_to_divides =
  ``!n m p : num.
      0 < p ==>
      logipedia_cong_congruent n m p ==>
      divides p (n - m)``;
