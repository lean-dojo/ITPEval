(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1982_a6:
  whether rearranging a conditionally constrained real series by a bijection
  of the positive integers preserves its limit. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1982_a6 =
  ``let positive = {n : num | 1 <= n}
    in
      ((!b : num -> num. !x : num -> real.
          BIJ b positive positive /\
          (!m n : num.
             m IN positive /\ n IN positive /\ m < n
             ==>
             abs (x n) < abs (x m)) /\
          (((\n : num.
               abs ((&(b n) : real) - &n) * abs (x n)) --> 0)
             sequentially) /\
          (((\n : num.
               SIGMA x (IMAGE SUC (count n))) --> 1)
             sequentially)
          ==>
          (((\n : num.
               SIGMA (\k : num. x (b k)) (IMAGE SUC (count n))) --> 1)
             sequentially))
       <=> F)``;
