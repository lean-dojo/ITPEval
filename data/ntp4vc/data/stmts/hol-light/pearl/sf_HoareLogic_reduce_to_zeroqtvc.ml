(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_reduce_to_zeroqtvc: the reduce-to-zero loop verification
  condition over unbounded integers, including invariant initialization,
  preservation, and strict descent. This file contains no proof.
*)

let statement =
 `!x:int.
    (&0:int) <= x
    ==>
    (&0:int) <= x /\
    (!x1:int.
       (&0:int) <= x1
       ==>
       if ~(x1 = (&0:int)) then
         ((&0:int) <= x1 /\ x1 - (&1:int) < x1) /\
         (&0:int) <= x1 - (&1:int)
       else
         x1 = (&0:int))`;;
