(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b1:
  the real sequence beginning at 1 and defined by a logarithmic-exponential
  recurrence has a convergent infinite series with sum exp 1 - 1. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory transcTheory;

val putnam_2016_b1 =
  ``!x : num -> real.
      x 0 = 1 /\
      (!n : num.
         x (n + 1) = ln (exp (x n) - x n))
      ==>
      summable x /\
      suminf x = exp 1 - 1``;
