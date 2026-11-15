(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b4:
  a globally three-times differentiable real function with continuous third
  derivative, positive value and first three derivatives, and third derivative
  bounded above by the function has first derivative less than twice the
  function everywhere. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory;

val putnam_1999_b4 =
  ``!f : real -> real.
      (!x : real. higher_differentiable 3 f x) /\
      (\x : real. diffn 3 f x) continuous_on UNIV /\
      (!x : real. 0 < f x) /\
      (!x : real. 0 < diffn 1 f x) /\
      (!x : real. 0 < diffn 2 f x) /\
      (!x : real. 0 < diffn 3 f x) /\
      (!x : real. diffn 3 f x <= f x)
      ==>
      !x : real. diffn 1 f x < 2 * f x``;
