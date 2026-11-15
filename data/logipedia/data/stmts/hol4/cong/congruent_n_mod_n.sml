(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_n_mod_n (catalog title "cong.congruent_n_mod_n"): every
  natural number is congruent modulo a positive natural modulus to its
  remainder modulo that modulus. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val cong_congruent_n_mod_n =
  ``!(n : num) (p : num).
      0 < p
      ==>
      logipedia_cong_congruent n (n MOD p) p``;
