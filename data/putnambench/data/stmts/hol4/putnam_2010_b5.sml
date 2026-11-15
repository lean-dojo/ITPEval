(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b5:
  nonexistence of a strictly increasing differentiable real function whose
  derivative at every point equals its value at its own value. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory derivativeTheory;

val putnam_2010_b5 =
  ``((?f : real -> real.
        (!x y : real. x < y ==> f x < f y) /\
        f differentiable_on UNIV /\
        (!x : real. vector_derivative f (at x) = f (f x)))
     <=> F)``;
