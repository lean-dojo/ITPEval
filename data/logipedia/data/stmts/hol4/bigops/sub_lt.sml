(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sub_lt, catalog title "bigops.sub_lt": an order-preserving identity
  embedding of Boolean-selected natural indices. This file contains no proof.
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

val bigops_sub_lt =
  ``!(e : num -> num) (p : num -> bool) (n : num) (m : num).
      n <= m
      ==>
      logipedia_bigops_sub_hk
        (\x : num. x) (\x : num. x) n m p p e e``;
