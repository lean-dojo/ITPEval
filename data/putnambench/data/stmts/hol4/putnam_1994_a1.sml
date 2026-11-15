(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a1:
  a positive real sequence satisfying a binary-tree lower bound has partial
  sums that grow without bound. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1994_a1 =
  ``!a : num -> real.
      (!n : num.
         1 <= n
         ==>
         0 < a n /\
         a n <= a (2 * n) + a (2 * n + 1))
      ==>
      !B : real.
        ?N : num.
          !n : num.
            N <= n
            ==>
            B <= SIGMA a (IMAGE SUC (count n))``;
