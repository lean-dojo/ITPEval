(*
  Statement-only formalization of Logipedia corpus artifact
  cong.divides_to_congruent (catalog title "cong.divides_to_congruent"):
  for natural numbers n, m, and positive p, if m is at most n and p divides
  their truncated difference n - m, then n and m are congruent modulo p.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_cong_congruent_def = new_definition (
  "logipedia_cong_congruent_def",
  ``logipedia_cong_congruent (n : num) (m : num) (p : num) <=>
      n MOD p = m MOD p``);

val cong_divides_to_congruent =
  ``!n m p : num.
      0 < p ==>
      m <= n ==>
      divides p (n - m) ==>
      logipedia_cong_congruent n m p``;
