(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sub0_to_false, catalog title "bigops.sub0_to_false": a Boolean
  selection predicate is false below its bound when its selected-index map
  embeds into a zero-sized target. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

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

val bigops_sub0_to_false =
  ``!(h : num -> num) (k : num -> num).
      !n1 n2 : num.
      !(p1 : num -> bool) (p2 : num -> bool).
      !(f1 : num -> num) (f2 : num -> num).
        n1 = 0
        ==>
        logipedia_bigops_sub_hk h k n2 n1 p2 p1 f2 f1
        ==>
        !i : num.
          i < n2
          ==>
          p2 i = F``;
