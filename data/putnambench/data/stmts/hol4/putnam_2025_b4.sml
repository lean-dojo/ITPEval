(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b4
  (putnambench__hol4__putnam_2025_b4): an upper bound on the sum of the
  entries of a nonnegative-integer square matrix with a triangular zero
  region and zero-or-one row and column increments. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val putnam_2025_b4 =
  ``!m : num. !A : num -> num -> num. !S N : num.
      let grid = count (m + 2) in
      let steps = count (m + 1) in
        (!i j : num.
           i IN grid /\ j IN grid /\ i + j <= m
           ==>
           A i j = 0) /\
        (!i j : num.
           i IN steps /\ j IN grid
           ==>
           A (i + 1) j = A i j \/
           A (i + 1) j = A i j + 1) /\
        (!i j : num.
           i IN grid /\ j IN steps
           ==>
           A i (j + 1) = A i j \/
           A i (j + 1) = A i j + 1) /\
        S =
          SIGMA
            (\i : num. SIGMA (\j : num. A i j) grid)
            grid /\
        N =
          CARD
            {ij : num # num |
               FST ij IN grid /\
               SND ij IN grid /\
               A (FST ij) (SND ij) <> 0}
        ==>
        3 * S <= (m + 4) * N``;
