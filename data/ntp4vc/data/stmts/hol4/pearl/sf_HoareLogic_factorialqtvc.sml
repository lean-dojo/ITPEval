(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_factorialqtvc: the factorial loop verification
  condition over integers, using the factorial base and positive-recursion
  equations to establish initialization and loop preservation. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val sf_HoareLogic_factorial_vc =
  ``!fact : int -> int.
      fact (0 : int) = (1 : int) ==>
      (!n : int.
        (0 : int) < n ==>
        fact n = n * fact (n - (1 : int))) ==>
      !x : int.
        (0 : int) <= x ==>
        (0 : int) <= x /\
        (1 : int) * fact x = fact x /\
        !z y : int.
          (0 : int) <= z /\ y * fact z = fact x ==>
          if ~(z = (0 : int)) then
            ((0 : int) <= z /\ z - (1 : int) < z) /\
            (0 : int) <= z - (1 : int) /\
            y * z * fact (z - (1 : int)) = fact x
          else
            y = fact x``;
