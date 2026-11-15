(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b5:
  a real function is continuous if and only if all of its naturally indexed
  integer-level clipped compositions are continuous. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_topologyTheory;

val putnam_1970_b5 =
  ``!ramp : int -> real -> real. !F : real -> real.
      ramp =
        (\n : int. \x : real.
           if x <= ~(real_of_int n) then
             ~(real_of_int n)
           else if ~(real_of_int n) < x /\ x <= real_of_int n then
             x
           else
             real_of_int n)
      ==>
      (F continuous_on UNIV <=>
       !n : num.
         (\x : real. ramp (int_of_num n) (F x)) continuous_on UNIV)``;
