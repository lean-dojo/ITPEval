(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_I_gen: shifting a Boolean-selected natural-number product by
  a lower bound equals filtering the original prefix to indices at or above
  that bound. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_bigops_nat_bigop_def = Define `
  (logipedia_bigops_nat_bigop 0 (p : num -> bool) (f : num -> num) = 1) /\
  (logipedia_bigops_nat_bigop (SUC n) p f =
    if p n then
      f n * logipedia_bigops_nat_bigop n p f
    else
      logipedia_bigops_nat_bigop n p f)
`;

val bigops_bigop_I_gen =
  ``!a b : num. !(p : num -> bool) (f : num -> num).
      a <= b
      ==>
      logipedia_bigops_nat_bigop
        (b - a)
        (\i. p (i + a))
        (\i. f (i + a)) =
      logipedia_bigops_nat_bigop
        b
        (\i. a <= i /\ p i)
        f``;
