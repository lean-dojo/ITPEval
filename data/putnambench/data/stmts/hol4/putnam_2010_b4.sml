(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b4:
  the affine real-polynomial pairs satisfying a unit finite-difference
  determinant identity are exactly those with coefficient determinant one.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory polyTheory;

val putnam_2010_b4 =
  ``!p q : real list.
      (!x : real.
         poly p x * poly q (x + 1) -
           poly p (x + 1) * poly q x =
         1)
      <=>
      ?a b c d : real.
        b * c - a * d = 1 /\
        (!x : real. poly p x = a * x + b) /\
        (!x : real. poly q x = c * x + d)``;
