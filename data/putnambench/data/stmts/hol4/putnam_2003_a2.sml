(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a2:
  the Minkowski inequality for the geometric means of two finite sequences
  of nonnegative real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_2003_a2 =
  ``!n : num. !a b : num -> real.
      0 < n /\
      (!i : num. i < n ==> 0 <= a i /\ 0 <= b i)
      ==>
      REAL_PROD_IMAGE a (count n) powr (1 / &n) +
        REAL_PROD_IMAGE b (count n) powr (1 / &n) <=
      REAL_PROD_IMAGE
        (\i : num. a i + b i)
        (count n) powr (1 / &n)``;
