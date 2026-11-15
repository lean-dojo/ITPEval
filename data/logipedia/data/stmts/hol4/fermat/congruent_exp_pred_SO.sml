(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_exp_pred_SO (catalog title
  "fermat.congruent_exp_pred_SO"): for natural numbers p and a, if p is
  prime and does not divide a, then a raised to the predecessor of p is
  congruent to 1 modulo p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val fermat_congruent_exp_pred_SO =
  ``!p : num.
      !a : num.
        prime p ==>
        ~divides p a ==>
        logipedia_cong_congruent (a EXP (PRE p)) 1 p``;
