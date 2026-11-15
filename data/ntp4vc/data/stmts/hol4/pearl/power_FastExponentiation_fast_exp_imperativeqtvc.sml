(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/power_FastExponentiation_fast_exp_imperativeqtvc: the imperative
  fast-exponentiation verification condition, including initialization,
  loop-invariant preservation, variant descent, and final correctness for a
  nonnegative integer exponent. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val power_FastExponentiation_fast_exp_imperative_vc =
  ``let int_power =
      \base : int. \exponent : int.
        base ** (if exponent < 0 then 0 else Num exponent)
    in
      !n x : int.
        0 <= n ==>
        (0 <= n /\
         (1 : int) * int_power x n = int_power x n /\
         (!e p r : int.
            0 <= e /\ r * int_power p e = int_power x n ==>
            if 0 < e then
              ~((2 : int) = 0) /\
              (let half = e quot 2
               in
                 if e rem 2 = 1 then
                   ~((2 : int) = 0) /\
                   ((0 <= e /\ half < e) /\ 0 <= half) /\
                   r * p * int_power (p * p) half = int_power x n
                 else
                   ~((2 : int) = 0) /\
                   ((0 <= e /\ half < e) /\ 0 <= half) /\
                   r * int_power (p * p) half = int_power x n)
            else
              r = int_power x n))``;
