(*
  Statement-only formalization of Logipedia corpus artifact
  cong.transitive_congruent (catalog title "cong.transitive_congruent"):
  congruence of natural numbers modulo any natural modulus is transitive.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val cong_transitive_congruent =
  ``!p x y z : num.
      logipedia_cong_congruent x y p ==>
      logipedia_cong_congruent y z p ==>
      logipedia_cong_congruent x z p``;
