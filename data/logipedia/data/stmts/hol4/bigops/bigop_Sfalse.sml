(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_Sfalse: a Boolean-selected polymorphic big operation is
  unchanged when extended by one index whose selector is false. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_bigops_bigop_def = Define `
  (logipedia_bigops_bigop 0 (p : num -> bool) (nil : 'a)
      (op : 'a -> 'a -> 'a) (f : num -> 'a) = nil) /\
  (logipedia_bigops_bigop (SUC n) p nil op f =
    if p n then
      op (f n) (logipedia_bigops_bigop n p nil op f)
    else
      logipedia_bigops_bigop n p nil op f)
`;

val bigops_bigop_Sfalse =
  ``!k : num.
      !(p : num -> bool) (nil : 'a)
        (op : 'a -> 'a -> 'a) (f : num -> 'a).
        p k = F
        ==>
        logipedia_bigops_bigop (SUC k) p nil op f =
        logipedia_bigops_bigop k p nil op f``;
