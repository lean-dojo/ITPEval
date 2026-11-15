(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_slow_additionqtvc: the slow-addition loop verification
  condition over unbounded integers, covering invariant initialization,
  decrement progress and preservation, and the exit equality. This file
  contains no proof.
*)

let statement =
  `!x z1:int.
     (&0:int) <= x
     ==>
     (&0:int) <= x /\
     (!z x1:int.
        (&0:int) <= x1 /\ z + x1 = z1 + x
        ==>
        if ~(x1 = (&0:int)) then
          ((&0:int) <= x1 /\ x1 - (&1:int) < x1) /\
          (&0:int) <= x1 - (&1:int) /\
          z + (&1:int) + (x1 - (&1:int)) = z1 + x
        else
          z = z1 + x)`;;
