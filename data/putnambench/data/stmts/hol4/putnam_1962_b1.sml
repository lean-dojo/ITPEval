(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b1:
  the binomial convolution identity for real falling factorials defined by
  finite products. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1962_b1 =
  ``!p : num -> real -> real. !x y : real. !n : num.
      p 0 = (\z : real. 1) /\
      (!m : num.
         0 < m
         ==>
         p m =
           (\z : real.
              REAL_PROD_IMAGE
                (\i : num. z - &i)
                (count m)))
      ==>
      p n (x + y) =
        SIGMA
          (\k : num.
             &(binomial n k) * p k x * p (n - k) y)
          (count (SUC n))``;
