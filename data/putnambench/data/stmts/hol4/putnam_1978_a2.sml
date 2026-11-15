(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a2:
  the determinant formula for a real square matrix with constant entries
  above and below the diagonal and arbitrary diagonal entries. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory fcpTheory realTheory real_sigmaTheory;
open determinantTheory;

val putnam_1978_a2 =
  ``!n : num. !a b : real. !c : num -> real.
    !A : real['N]['N]. !p : real -> real.
      n = dimindex (:'N) /\
      0 < n /\
      a <> b /\
      A =
        (FCP i j.
           if i < j then a
           else if i > j then b
           else c i) /\
      (!x : real.
         p x = real_sigma$product (count n) (\i. c i - x))
      ==>
      determinant$det A = (b * p a - a * p b) / (b - a)``;
