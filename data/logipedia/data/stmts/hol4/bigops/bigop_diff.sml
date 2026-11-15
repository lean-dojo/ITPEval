(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_diff: a selected factor in a Boolean-filtered natural-number
  product below a bound can be factored out, leaving that index excluded from
  the remaining product. This file contains no proof.
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

val bigops_bigop_diff =
  ``!(p : num -> bool) (f : num -> num) (i : num) (n : num).
      i < n
      ==>
      p i = T
      ==>
      logipedia_bigops_nat_bigop n p f =
      f i *
        logipedia_bigops_nat_bigop
          n
          (\x. i <> x /\ p x)
          f``;
