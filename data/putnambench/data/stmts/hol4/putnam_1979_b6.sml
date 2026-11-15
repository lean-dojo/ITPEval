(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1979_b6:
  the absolute real part of a square root of a finite sum of complex squares
  is bounded by the sum of the absolute real parts. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory complexTheory;

val putnam_1979_b6 =
  ``!n : num. !z : num -> complex. !w : complex.
      w pow 2 =
        ITSET
          (\i acc. z i pow 2 + acc)
          (count n)
          (0 : complex)
      ==>
      abs (RE w) <=
        REAL_SUM_IMAGE (\i : num. abs (RE (z i))) (count n)``;
