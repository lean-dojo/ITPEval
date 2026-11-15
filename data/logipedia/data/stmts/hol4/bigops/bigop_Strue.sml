(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_Strue: a Boolean-selected polymorphic big operation extended
  by one index whose selector is true applies the binary operation to the new
  value and the preceding big operation. This file contains no proof.
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

val bigops_bigop_Strue =
  ``!k : num.
      !(p : num -> bool) (nil : 'a)
        (combine : 'a -> 'a -> 'a) (f : num -> 'a).
        p k = T
        ==>
        logipedia_bigops_bigop (SUC k) p nil combine f =
        combine (f k) (logipedia_bigops_bigop k p nil combine f)``;
