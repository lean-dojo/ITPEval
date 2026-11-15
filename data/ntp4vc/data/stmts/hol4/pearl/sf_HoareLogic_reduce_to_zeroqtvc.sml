(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_reduce_to_zeroqtvc: the reduce-to-zero loop
  verification condition over integers, asserting invariant initialization,
  strict variant decrease, and invariant preservation under decrement. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val sf_HoareLogic_reduce_to_zero_vc =
  ``!x : int.
      (0 : int) <= x ==>
      (0 : int) <= x /\
      !x1 : int.
        (0 : int) <= x1 ==>
        if ~(x1 = (0 : int)) then
          ((0 : int) <= x1 /\ x1 - (1 : int) < x1) /\
          (0 : int) <= x1 - (1 : int)
        else
          x1 = (0 : int)``;
