(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a6:
  a twice continuously differentiable real function bounded in absolute value
  by one, with prescribed squared initial value and derivative, has a point
  where its value plus second derivative vanishes. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory;

val putnam_1976_a6 =
  ``!f : real -> real.
      (!x : real. higher_differentiable 2 f x) /\
      (diffn 2 f) continuous_on UNIV /\
      (!x : real. abs (f x) <= 1) /\
      (f 0) pow 2 + (diffn 1 f 0) pow 2 = 4
      ==>
      ?y : real. f y + diffn 2 f y = 0``;
