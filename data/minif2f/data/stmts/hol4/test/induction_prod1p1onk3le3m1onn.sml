(*
  Statement-only formalization of miniF2F test problem induction_prod1p1onk3le3m1onn: for every
  positive natural n, the real product of 1 + 1 / k^3 from k = 1 through n is at most
  3 - 1 / n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val induction_prod1p1onk3le3m1onn =
  Parse.Term
    [QUOTE
       ("!n : num. " ^
        "0 < n ==> " ^
        "REAL_PROD_IMAGE " ^
        "(\\k. 1 + 1 / ((&(k + 1) : real) pow 3)) " ^
        "(count n) <= 3 - 1 / (&n : real)")];
