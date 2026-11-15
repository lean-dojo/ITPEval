(*
  Statement-only formalization of miniF2F valid problem amc12a_2002_p21: a modulo-10
  recurrence applying at every natural index whose initial partial sums cannot
  exceed 10000 before index 1999. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val amc12a_2002_p21 =
  ``!u : num -> num.
      u 0 = 4 /\
      u 1 = 7 /\
      (!n : num.
         u (n + 2) = (u n + u (n + 1)) MOD 10)
      ==>
      !n : num.
        SIGMA u (count n) > 10000 ==>
        1999 <= n``;
