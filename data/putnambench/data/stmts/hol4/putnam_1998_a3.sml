(*
  Statement-only formalization of PutnamBench artifact putnam_1998_a3:
  a real function with continuous third derivative has a point where the
  product of its value and first three derivatives is nonnegative. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory;

val putnam_1998_a3 =
  ``!f : real -> real.
      (!x : real. higher_differentiable 3 f x) /\
      (\x : real. diffn 3 f x) continuous_on UNIV
      ==>
      ?a : real.
        0 <= f a * diffn 1 f a * diffn 2 f a * diffn 3 f a``;
