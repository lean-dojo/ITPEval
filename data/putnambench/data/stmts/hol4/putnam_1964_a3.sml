(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a3:
  an identity for the infinite sum of products of the two subinterval lengths
  created by successively inserting distinct dense points in (0,1). This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory seqTheory;

val putnam_1964_a3 =
  ``!x a b : num -> real.
      IMAGE x UNIV SUBSET {r : real | 0 < r /\ r < 1} /\
      {r : real | 0 < r /\ r < 1} SUBSET closure (IMAGE x UNIV) /\
      INJ x UNIV UNIV /\
      a =
        (\n : num.
           x n -
           @p : real.
             (p = 0 \/
              (p < x n /\ ?i : num. i < n /\ p = x i)) /\
             (!q : real.
                (q = 0 \/
                 (q < x n /\ ?i : num. i < n /\ q = x i))
                ==>
                q <= p)) /\
      b =
        (\n : num.
           (@p : real.
              (p = 1 \/
               (x n < p /\ ?i : num. i < n /\ p = x i)) /\
              (!q : real.
                 (q = 1 \/
                  (x n < q /\ ?i : num. i < n /\ q = x i))
                 ==>
                 p <= q)) -
           x n)
      ==>
      suminf (\n : num. a n * b n * (a n + b n)) = 1 / 3``;
