(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a5:
  evaluation of the finite sum of squared indices weighted by binomial
  coefficients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory listTheory;

val putnam_1962_a5 =
  ``!n : num.
      2 <= n
      ==>
      n * (n + 1) * 2 ** (n - 2) =
        SUM
          (GENLIST
             (\i. binomial n (SUC i) * (SUC i) ** 2)
             n)``;
