(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sameF_p_le: Boolean-filtered pointwise agreement below a natural
  bound is preserved when the bound is decreased. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_bigops_sameF_p_def = new_definition (
  "logipedia_bigops_sameF_p_def",
  ``logipedia_bigops_sameF_p (k : num) (p : num -> bool)
      (f : num -> 'a) (g : num -> 'a) <=>
      !i. i < k ==> p i = T ==> f i = g i``);

val bigops_sameF_p_le =
  ``!(p : num -> bool) (f : num -> 'a) (g : num -> 'a)
      (n : num) (m : num).
      n <= m ==>
      logipedia_bigops_sameF_p m p f g ==>
      logipedia_bigops_sameF_p n p f g``;
