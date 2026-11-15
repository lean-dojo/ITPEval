(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a4:
  a fixed finite rational linear combination of nth powers of linear forms
  with coefficients minus one, zero, or one represents the product identity
  for every assignment of the real variables. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory ratTheory realTheory real_of_ratTheory
     real_sigmaTheory;

val putnam_2004_a4 =
  ``!n : num.
      0 < n
      ==>
      ?N : num. ?c : num -> rat. ?a : num -> num -> real.
        (!i j : num.
           i < N /\ j < n
           ==>
           (a i j = -1 \/ a i j = 0 \/ a i j = 1)) /\
        (!x : num -> real.
           REAL_PROD_IMAGE x (count n) =
             SIGMA
               (\i : num.
                  real_of_rat (c i) *
                  (SIGMA
                     (\j : num. a i j * x j)
                     (count n)) pow n)
               (count N))``;
