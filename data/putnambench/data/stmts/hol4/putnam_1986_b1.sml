(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b1:
  positive real base and height satisfying the unit-circle and equal-area
  equations have height 2/5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1986_b1 =
  ``!b h : real.
      0 < b /\
      0 < h /\
      b pow 2 + h pow 2 = 2 pow 2 /\
      b * h = (1 / 2) * b * (1 - h / 2)
      ==>
      h = 2 / 5``;
