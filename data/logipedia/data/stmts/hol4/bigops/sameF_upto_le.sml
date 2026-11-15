(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sameF_upto_le: pointwise agreement below a natural bound is preserved
  when the bound is decreased. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_bigops_sameF_upto_def = new_definition (
  "logipedia_bigops_sameF_upto_def",
  ``logipedia_bigops_sameF_upto (k : num)
      (f : num -> 'a) (g : num -> 'a) <=>
      !i. i < k ==> f i = g i``);

val bigops_sameF_upto_le =
  ``!(f : num -> 'a) (g : num -> 'a) (n : num) (m : num).
      n <= m ==>
      logipedia_bigops_sameF_upto m f g ==>
      logipedia_bigops_sameF_upto n f g``;
