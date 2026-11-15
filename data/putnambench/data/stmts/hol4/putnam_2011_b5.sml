(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b5:
  a uniform linear bound on whole-real-line integrals of squared finite sums
  of Cauchy kernels implies a positive cubic lower bound for the associated
  double sums. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory integrationTheory;

val putnam_2011_b5 =
  ``!a : num -> real.
      (?A : real.
         !n : num.
           integration$integral UNIV
             (\x : real.
                (SIGMA
                   (\i : num. 1 / (1 + (x - a i) pow 2))
                   (count n)) pow 2) <=
           A * &n)
      ==>
      ?B : real.
        0 < B /\
        !n : num.
          B * (&n) pow 3 <=
          SIGMA
            (\i : num.
               SIGMA
                 (\j : num. 1 + (a i - a j) pow 2)
                 (count n))
            (count n)``;
