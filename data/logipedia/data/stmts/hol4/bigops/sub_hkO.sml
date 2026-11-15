(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sub_hkO, catalog title "bigops.sub_hkO": the selected-index embedding
  relation sub_hk holds when its source bound is zero. This file contains no
  proof.
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

val bigops_sub_hkO =
  ``!(h : num -> num) (k : num -> num).
      !n1 n2 : num.
      !(p1 : num -> bool) (p2 : num -> bool).
      !(f1 : num -> num) (f2 : num -> num).
        n1 = 0
        ==>
        logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2``;
