(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a6:
  positive contact coordinates for the line and real-power curve exist
  exactly when the coefficients satisfy the conjugate-exponent equation.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_1965_a6 =
  ``!u v m : real.
      0 < u /\ 0 < v /\ 1 < m
      ==>
      ((?x y : real.
          0 < x /\
          0 < y /\
          u * x + v * y = 1 /\
          x powr m + y powr m = 1 /\
          u = x powr (m - 1) /\
          v = y powr (m - 1))
       <=>
       ?n : real.
         u powr n + v powr n = 1 /\
         1 / m + 1 / n = 1)``;
