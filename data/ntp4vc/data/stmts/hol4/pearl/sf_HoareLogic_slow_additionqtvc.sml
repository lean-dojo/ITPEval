(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_slow_additionqtvc: the slow-addition loop verification
  condition over unbounded integers, preserving nonnegativity and the
  invariant z + x1 = z1 + x through decrement and at loop exit. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val sf_HoareLogic_slow_addition_vc =
  ``!x z1 : int.
      (0 : int) <= x ==>
      (0 : int) <= x /\
      !z x1 : int.
        (0 : int) <= x1 /\ z + x1 = z1 + x ==>
        if ~(x1 = (0 : int)) then
          ((0 : int) <= x1 /\ x1 - (1 : int) < x1) /\
          (0 : int) <= x1 - (1 : int) /\
          z + (1 : int) + (x1 - (1 : int)) = z1 + x
        else
          z = z1 + x``;
