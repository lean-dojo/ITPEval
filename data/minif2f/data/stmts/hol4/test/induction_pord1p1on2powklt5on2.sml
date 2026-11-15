(*
  Statement-only formalization of miniF2F test problem induction_pord1p1on2powklt5on2: for every
  positive natural n, the real product of 1 + 1 / 2^k from k = 1 through n is less than 5 / 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val induction_pord1p1on2powklt5on2 =
  ``!n : num.
      0 < n
      ==>
      REAL_PROD_IMAGE
        (\k. 1 + 1 / ((2 : real) pow (k + 1)))
        (count n) < 5 / 2``;
