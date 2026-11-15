(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b6:
  a bounded real function on the closed unit disk with both partial
  derivatives everywhere has an interior point where the sum of their
  squares is at most sixteen. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val putnam_1967_b6 =
  ``!f : real -> real -> real.
      (!x y : real.
         higher_differentiable 1 (\t : real. f t y) x /\
         higher_differentiable 1 (\t : real. f x t) y) /\
      (!x y : real.
         x pow 2 + y pow 2 <= 1
         ==>
         abs (f x y) <= 1)
      ==>
      ?x0 y0 : real.
        x0 pow 2 + y0 pow 2 < 1 /\
        (diffn 1 (\x : real. f x y0) x0) pow 2 +
          (diffn 1 (\y : real. f x0 y) y0) pow 2 <= 16``;
