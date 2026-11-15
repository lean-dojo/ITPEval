(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_times (catalog title "cong.congruent_times"):
  natural-number congruence modulo a positive modulus is preserved when
  congruent factors are multiplied. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val cong_congruent_times =
  ``!n m n1 m1 p : num.
      0 < p ==>
      logipedia_cong_congruent n n1 p ==>
      logipedia_cong_congruent m m1 p ==>
      logipedia_cong_congruent (n * m) (n1 * m1) p``;
