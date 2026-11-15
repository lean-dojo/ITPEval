(*
  Statement-only formalization of Hundred Theorems artifact 073, "Ascending or
  Descending Sequences (Erdős–Szekeres)": every sequence of m*n+1 elements of
  a linearly ordered type has a nondecreasing subsequence of length m+1 or a
  nonincreasing subsequence of length n+1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val erdos_szekeres =
  ``let is_linear_order =
      \(le : 'a -> 'a -> bool).
        (!x. le x x) /\
        (!x y z. le x y /\ le y z ==> le x z) /\
        (!x y. le x y /\ le y x ==> x = y) /\
        (!x y. le x y \/ le y x)
    in
    let monotone_on =
      \(le : 'a -> 'a -> bool) (f : num -> 'a) (s : num set).
        !i j. i IN s /\ j IN s /\ i <= j ==> le (f i) (f j)
    in
      !(le : 'a -> 'a -> bool) (f : num -> 'a) (m : num) (n : num).
        is_linear_order le ==>
        (?s : num set.
           s SUBSET count (m * n + 1) /\
           CARD s = m + 1 /\
           monotone_on le f s) \/
        (?s : num set.
           s SUBSET count (m * n + 1) /\
           CARD s = n + 1 /\
           monotone_on (\x y. le y x) f s)``;
