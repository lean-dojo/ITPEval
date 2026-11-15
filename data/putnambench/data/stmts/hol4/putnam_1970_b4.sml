(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b4:
  a twice-differentiable real function on the closed unit interval satisfying
  endpoint and first-derivative bounds has a point where the second derivative
  has magnitude at least nine halves. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val putnam_1970_b4 =
  ``!x : real -> real.
      (!t : real.
         0 <= t /\ t <= 1
         ==>
         higher_differentiable 2 x t) /\
      x 1 - x 0 = 1 /\
      diffn 1 x 0 = 0 /\
      diffn 1 x 1 = 0 /\
      (!t : real.
         0 < t /\ t < 1
         ==>
         abs (diffn 1 x t) <= 3 / 2)
      ==>
      ?t : real.
        0 <= t /\ t <= 1 /\
        9 / 2 <= abs (diffn 2 x t)``;
