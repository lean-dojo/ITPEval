(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b4:
  for every positive integer n, all complex roots of the polynomial whose
  coefficient of x^k is 2^(k*(n-k)) are real. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory complexTheory;

val putnam_2014_b4 =
  ``!n : num.
      0 < n
      ==>
      !z : complex.
        ITSET
          (\k acc.
             (2 : complex) pow (k * (n - k)) * z pow k + acc)
          (count (n + 1))
          0 =
        0
        ==>
        IM z = 0``;
