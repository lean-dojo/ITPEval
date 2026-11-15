(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a3:
  pi / 2 is the smallest positive real zero-time attainable by two globally
  differentiable real functions satisfying the coupled absolute derivative
  bounds and the stated initial conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory derivativeTheory;

val putnam_2023_a3 =
  ``let admissible =
      \r : real.
        ?f g : real -> real.
          f differentiable_on UNIV /\
          g differentiable_on UNIV /\
          f 0 > 0 /\
          g 0 = 0 /\
          (!x : real.
             abs (vector_derivative f (at x)) <= abs (g x) /\
             abs (vector_derivative g (at x)) <= abs (f x)) /\
          f r = 0
    in
    let solution = (pi / 2 : real)
    in
      0 < solution /\
      admissible solution /\
      (!r : real.
         0 < r /\ r < solution
         ==>
         ~admissible r)``;
