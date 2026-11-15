(*
  Statement-only formalization of miniF2F test problem
  numbertheory_exk2powkeqapb2mulbpa2_aeq1: positive natural numbers satisfying
  the given exponential Diophantine factorization must have a = 1. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val numbertheory_exk2powkeqapb2mulbpa2_aeq1 =
  ``!a b : num.
      0 < a /\
      0 < b /\
      (?k : num.
         0 < k /\
         2 EXP k = (a + b EXP 2) * (b + a EXP 2))
      ==>
      a = 1``;
