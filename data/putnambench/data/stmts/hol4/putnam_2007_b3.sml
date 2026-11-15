(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b3:
  the closed form for the 2007th term of a real sequence defined using the
  floor of its current term times the square root of five. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory transcTheory;

val putnam_2007_b3 =
  ``!x : num -> real.
      x 0 = 1 /\
      (!n : num.
         x (n + 1) =
           3 * x n +
           real_of_int (INT_FLOOR (x n * sqrt 5)))
      ==>
      let a = (1 + sqrt 5) / 2
      in
        x 2007 =
          (2 pow 2006 / sqrt 5) *
          (a pow 4017 + 1 / (a pow 4017))``;
