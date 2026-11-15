(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a3:
  the minimum over real x of the absolute value of the stated sum of
  trigonometric functions and reciprocals is 2 * sqrt 2 - 1. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_2003_a3 =
  ``let f =
      \x : real.
        abs
          (sin x + cos x + tan x +
           1 / tan x + 1 / cos x + 1 / sin x)
    in
    let m = 2 * sqrt 2 - 1
    in
      (?x : real. f x = m) /\
      (!x : real. m <= f x)``;
