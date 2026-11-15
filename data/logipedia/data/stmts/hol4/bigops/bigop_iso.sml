(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_iso, catalog title "bigops.bigop_iso": Boolean-filtered finite
  products of natural numbers are invariant under the source's isomorphism of
  selected indices. This file contains no proof.
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

val logipedia_bigops_sub_hk_def = Define `
  logipedia_bigops_sub_hk
    (h : num -> num)
    (k : num -> num)
    (n1 : num)
    (n2 : num)
    (p1 : num -> bool)
    (p2 : num -> bool)
    (f1 : num -> num)
    (f2 : num -> num) <=>
  !i : num.
    i < n1
    ==>
    p1 i = T
    ==>
    (h i < n2 /\ p2 (h i) = T) /\ k (h i) = i
`;

val logipedia_bigops_iso_def = Define `
  logipedia_bigops_iso
    (n1 : num)
    (n2 : num)
    (p1 : num -> bool)
    (p2 : num -> bool)
    (f1 : num -> num)
    (f2 : num -> num) <=>
  ?h k : num -> num.
    ((!i : num.
        i < n1
        ==>
        p1 i = T
        ==>
        f1 i = f2 (h i)) /\
      logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2) /\
    logipedia_bigops_sub_hk k h n2 n1 p2 p1 f2 f1
`;

val bigops_bigop_iso =
  ``!n1 n2 : num.
      !(p1 : num -> bool) (p2 : num -> bool).
      !(f1 : num -> num) (f2 : num -> num).
        logipedia_bigops_iso n1 n2 p1 p2 f1 f2
        ==>
        logipedia_bigops_nat_bigop n1 p1 f1 =
        logipedia_bigops_nat_bigop n2 p2 f2``;
