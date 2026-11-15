(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.transitive_sub, catalog title "bigops.transitive_sub": transitivity
  of the selected-index embedding relation under composition of its forward
  and inverse maps. This file contains no proof.
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

val bigops_transitive_sub =
  ``!(h1 : num -> num) (k1 : num -> num).
      !(h2 : num -> num) (k2 : num -> num).
      !n1 n2 n3 : num.
      !(p1 : num -> bool) (p2 : num -> bool) (p3 : num -> bool).
      !(f1 : num -> num) (f2 : num -> num) (f3 : num -> num).
        logipedia_bigops_sub_hk h1 k1 n1 n2 p1 p2 f1 f2
        ==>
        logipedia_bigops_sub_hk h2 k2 n2 n3 p2 p3 f2 f3
        ==>
        logipedia_bigops_sub_hk
          (\x : num. h2 (h1 x))
          (\x : num. k1 (k2 x))
          n1 n3 p1 p3 f1 f3``;
