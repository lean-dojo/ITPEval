(*
  Statement-only formalization of miniF2F valid problem
  numbertheory_nckeqnm1ckpnm1ckm1: Pascal's recurrence for binomial
  coefficients over natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory;

val numbertheory_nckeqnm1ckpnm1ckm1 =
  ``!n k : num.
      0 < n /\
      0 < k /\
      k <= n
      ==>
      binomial n k =
        binomial (n - 1) k + binomial (n - 1) (k - 1)``;
