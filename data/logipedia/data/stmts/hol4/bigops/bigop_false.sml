(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_false: a Boolean-selected polymorphic big operation whose
  selector is constantly false returns its supplied identity element.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_bigops_bigop_def = Define `
  (logipedia_bigops_bigop 0 (p : num -> bool) (nil : 'a)
      (combine : 'a -> 'a -> 'a) (f : num -> 'a) = nil) /\
  (logipedia_bigops_bigop (SUC n) p nil combine f =
    if p n then
      combine (f n) (logipedia_bigops_bigop n p nil combine f)
    else
      logipedia_bigops_bigop n p nil combine f)
`;

val bigops_bigop_false =
  ``!n : num.
      !(nil : 'a) (combine : 'a -> 'a -> 'a) (f : num -> 'a).
        logipedia_bigops_bigop n (\i. F) nil combine f = nil``;
