(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a2:
  a nonzero real sequence whose adjacent-term determinant is one admits a
  constant-coefficient second-order recurrence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val putnam_1993_a2 =
  ``!x : num -> real.
      (!n : num. x n <> 0) /\
      (!n : num.
         1 <= n
         ==>
         x n pow 2 - x (n - 1) * x (n + 1) = 1)
      ==>
      ?a : real.
        !n : num.
          1 <= n
          ==>
          x (n + 1) = a * x n - x (n - 1)``;
