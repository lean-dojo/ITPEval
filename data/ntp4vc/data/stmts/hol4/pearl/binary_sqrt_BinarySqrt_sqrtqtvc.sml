(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binary_sqrt_BinarySqrt_sqrtqtvc: a binary square-root routine's
  verification condition, relating its Boolean branch, ceiling-based integer
  invariant, and real square-root error interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val sqrt_vc =
  ``!r eps0 : real. !n : int. !o1 : bool.
      0 <= r ==>
      0 < eps0 ==>
      (1 : int) <= n ==>
      (if r < real_of_int n * eps0 then
         o1 =
           (if (1 : real) < real_of_int n * eps0 then T else F)
       else
         o1 = F) ==>
      (~(o1 = T) ==>
       (let o2 = (2 : int) * n in
          (0 : int) <= INT_CEILING (max r (1 : real) / eps0) - n /\
          INT_CEILING (max r (1 : real) / eps0) - o2 <
            INT_CEILING (max r (1 : real) / eps0) - n /\
          (0 : real) <= r /\
          (0 : real) < eps0 /\
          (1 : int) <= o2 /\
          (2 : real) * (real_of_int n * eps0) =
            real_of_int o2 * eps0)) /\
      (!result : real.
         (if o1 = T then
            result = (0 : real)
          else
            let o2 = (2 : real) * (real_of_int n * eps0)
            in
              ?r' : real.
                (r' * r' <= r /\ r < (r' + o2) * (r' + o2)) /\
                (if
                   (r' + real_of_int n * eps0) *
                       (r' + real_of_int n * eps0) <= r
                 then
                   result = r' + real_of_int n * eps0
                 else
                   result = r')) ==>
         result * result <= r /\
         r <
           (result + real_of_int n * eps0) *
             (result + real_of_int n * eps0))``;
