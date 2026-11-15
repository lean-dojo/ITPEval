(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/power_FastExponentiation_fast_exp_2qtvc: the fast-exponentiation
  verification condition for accumulator recursion, including recursive
  descent obligations and preservation of the integer-power result. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val power_FastExponentiation_fast_exp_2_vc =
  ``let int_power =
      \base : int. \exponent : int.
        base ** (if exponent < 0 then 0 else Num exponent)
    in
      !n acc x : int.
        0 <= n ==>
        ((~(n = 0) ==>
          ~((2 : int) = 0) /\
          (if n rem 2 = 0 then
             ~((2 : int) = 0) /\
             (let o1 = n quot 2
              in
                ((0 <= n /\ o1 < n) /\ 0 <= o1))
           else
             let o1 = n - 1
             in
               ((0 <= n /\ o1 < n) /\ 0 <= o1))) /\
         (!result : int.
            (if n = 0 then
               result = acc
             else if n rem 2 = 0 then
               result = int_power (x * x) (n quot 2) * acc
             else
               result = int_power x (n - 1) * (x * acc)) ==>
            result = int_power x n * acc))``;
