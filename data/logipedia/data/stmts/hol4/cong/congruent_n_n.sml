(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_n_n (catalog title "cong.congruent_n_n"): every natural
  number is congruent to itself modulo every natural modulus. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val cong_congruent_n_n =
  ``!(n : num) (p : num).
      logipedia_cong_congruent n n p``;
