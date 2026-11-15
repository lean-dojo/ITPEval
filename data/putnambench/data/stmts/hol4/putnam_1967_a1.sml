(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a1:
  a real sine polynomial bounded pointwise by the absolute value of sine has
  the absolute value of its weighted coefficient sum at most one. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_1967_a1 =
  ``!n : num. !a : num -> real. !f : real -> real.
      0 < n /\
      f =
        (\x : real.
           SIGMA
             (\i : num. a i * sin (&i * x))
             (IMAGE SUC (count n))) /\
      (!x : real. abs (f x) <= abs (sin x))
      ==>
      abs
        (SIGMA
           (\i : num. &i * a i)
           (IMAGE SUC (count n))) <=
      1``;
