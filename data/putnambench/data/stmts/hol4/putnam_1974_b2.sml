(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b2:
  a continuously differentiable real function whose squared derivative plus
  cubed value tends to zero at positive infinity has both its value and
  derivative tend to zero there. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory;

val putnam_1974_b2 =
  ``!y : real -> real.
      (!x : real. higher_differentiable 1 y x) /\
      (\x : real. diffn 1 y x) continuous_on UNIV /\
      (((\x : real. (diffn 1 y x) pow 2 + (y x) pow 3) --> 0)
        at_posinfinity)
      ==>
      (y --> 0) at_posinfinity /\
      (((\x : real. diffn 1 y x) --> 0) at_posinfinity)``;
