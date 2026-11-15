(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b2:
  for real x and y, if y is nonnegative and y*(y+1) <= (x+1)^2, then
  y*(y-1) <= x^2; the prescribed truth value is true. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1988_b2 =
  ``((!x y : real.
        0 <= y /\
        y * (y + 1) <= (x + 1) pow 2
        ==>
        y * (y - 1) <= x pow 2)
     <=> T)``;
