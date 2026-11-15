(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/gcd_vc_sp_BinaryGcd_binary_gcdqtvc: the binary-GCD verification
  condition for recursive-call descent and preservation of the integer
  greatest common divisor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory gcdTheory;

val gcd_vc_sp_BinaryGcd_binary_gcd_vc =
  ``let int_gcd =
      \a : int. \b : int. &(gcd (Num (ABS a)) (Num (ABS b)))
    in
      !u v : int.
        (0 : int) <= u ==>
        (0 : int) <= v ==>
        ((if u < v then
            (((0 : int) <= v /\ u < v) \/
             (v = u /\ (0 : int) <= u /\ v < u)) /\
            (0 : int) <= v /\
            (0 : int) <= u
          else
            ~(v = (0 : int)) ==>
            ~((2 : int) = (0 : int)) /\
            (if u rem (2 : int) = (0 : int) then
               ~((2 : int) = (0 : int)) /\
               (if v rem (2 : int) = (0 : int) then
                  ~((2 : int) = (0 : int)) /\
                  (let o1 = v quot (2 : int)
                   in
                     ~((2 : int) = (0 : int)) /\
                     (let o2 = u quot (2 : int)
                      in
                        (((0 : int) <= v /\ o1 < v) \/
                         (v = o1 /\ (0 : int) <= u /\ o2 < u)) /\
                        (0 : int) <= o2 /\
                        (0 : int) <= o1))
                else
                  ~((2 : int) = (0 : int)) /\
                  (let o1 = u quot (2 : int)
                   in
                     ((0 : int) <= u /\ o1 < u) /\
                     (0 : int) <= o1 /\
                     (0 : int) <= v))
             else
               ~((2 : int) = (0 : int)) /\
               (if v rem (2 : int) = (0 : int) then
                  ~((2 : int) = (0 : int)) /\
                  (let o1 = v quot (2 : int)
                   in
                     ((0 : int) <= v /\ o1 < v) /\
                     (0 : int) <= u /\
                     (0 : int) <= o1)
                else
                  ~((2 : int) = (0 : int)) /\
                  (let o1 = (u - v) quot (2 : int)
                   in
                     ((0 : int) <= u /\ o1 < u) /\
                     (0 : int) <= o1 /\
                     (0 : int) <= v)))) /\
         (!result : int.
            (if u < v then
               result = int_gcd v u
             else if v = (0 : int) then
               result = u
             else if u rem (2 : int) = (0 : int) then
               if v rem (2 : int) = (0 : int) then
                 result =
                   (2 : int) *
                   int_gcd
                     (u quot (2 : int))
                     (v quot (2 : int))
               else
                 result = int_gcd (u quot (2 : int)) v
             else if v rem (2 : int) = (0 : int) then
               result = int_gcd u (v quot (2 : int))
             else
               result = int_gcd ((u - v) quot (2 : int)) v) ==>
            result = int_gcd u v))``;
