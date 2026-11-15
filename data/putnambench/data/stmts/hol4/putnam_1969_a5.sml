(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a5:
  equal initial values characterize when a continuous control can drive the
  globally differentiable solutions of the coupled linear differential
  equations to the origin at a prescribed positive time. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory;

val putnam_1969_a5 =
  ``!x0 y0 t : real.
      0 < t
      ==>
      (x0 = y0 <=>
       ?x y u : real -> real.
         (!p : real. x differentiable p) /\
         (!p : real. y differentiable p) /\
         u continuous_on UNIV /\
         (!p : real. (x diffl (-2 * y p + u p)) p) /\
         (!p : real. (y diffl (-2 * x p + u p)) p) /\
         x 0 = x0 /\
         y 0 = y0 /\
         x t = 0 /\
         y t = 0)``;
