(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.same_bigop: two Boolean-selected polymorphic big operations are equal
  when their selectors agree below the bound and their selected values agree.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_bigops_sameF_upto_def = new_definition (
  "logipedia_bigops_sameF_upto_def",
  ``logipedia_bigops_sameF_upto (k : num)
      (f : num -> 'a) (g : num -> 'a) <=>
      !i. i < k ==> f i = g i``);

val logipedia_bigops_sameF_p_def = new_definition (
  "logipedia_bigops_sameF_p_def",
  ``logipedia_bigops_sameF_p (k : num) (p : num -> bool)
      (f : num -> 'a) (g : num -> 'a) <=>
      !i. i < k ==> p i = T ==> f i = g i``);

val logipedia_bigops_bigop_def = Define `
  (logipedia_bigops_bigop 0 (p : num -> bool) (nil : 'a)
      (combine : 'a -> 'a -> 'a) (f : num -> 'a) = nil) /\
  (logipedia_bigops_bigop (SUC n) p nil combine f =
    if p n then
      combine (f n) (logipedia_bigops_bigop n p nil combine f)
    else
      logipedia_bigops_bigop n p nil combine f)
`;

val bigops_same_bigop =
  ``!k : num.
      !(p1 : num -> bool) (p2 : num -> bool) (nil : 'a)
        (combine : 'a -> 'a -> 'a) (f : num -> 'a) (g : num -> 'a).
        logipedia_bigops_sameF_upto k p1 p2 ==>
        logipedia_bigops_sameF_p k p1 f g ==>
        logipedia_bigops_bigop k p1 nil combine f =
        logipedia_bigops_bigop k p2 nil combine g``;
