(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a4:
  an all-ones a-by-b submatrix of an n-by-n real sign matrix with mutually
  orthogonal rows satisfies a * b <= n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2005_a4 =
  ``!n a b : num. !H S : num -> num -> real.
      1 <= n /\
      (!i j : num.
         i < n /\ j < n
         ==>
         H i j = 1 \/ H i j = -1) /\
      (!i j : num.
         i < n /\ j < n /\ i <> j
         ==>
         SIGMA (\k : num. H i k * H j k) (count n) = 0) /\
      1 <= a /\ a <= n /\ 1 <= b /\ b <= n /\
      (?rri cri : num -> num.
         (!i : num. i < a ==> rri i < n) /\
         (!i j : num.
            i < a /\ j < a /\ rri i = rri j
            ==>
            i = j) /\
         (!i : num. i < b ==> cri i < n) /\
         (!i j : num.
            i < b /\ j < b /\ cri i = cri j
            ==>
            i = j) /\
         (!i j : num.
            i < a /\ j < b
            ==>
            S i j = H (rri i) (cri j))) /\
      (!i j : num.
         i < a /\ j < b
         ==>
         S i j = 1)
      ==>
      a * b <= n``;
