(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/largest_prime_factor_PrimeFactor_smallest_divisorqtvc: the integer
  smallest-divisor verification condition for advancing a divisor search and
  returning a divisor with no smaller divisor from two onward. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val lpf_divides_def = Define `
  lpf_divides (divisor : int) (value : int) <=>
    ?factor : int. value = divisor * factor`;

val largest_prime_factor_PrimeFactor_smallest_divisor_vc =
  ``!n d : int.
      (2 : int) <= n ==>
      (2 : int) <= d ==>
      d <= n ==>
      (!i : int.
         (2 : int) <= i /\ i < d ==>
         ~lpf_divides i n) ==>
      (let o1 = d * d
       in
         (~(n < o1) ==>
          (((2 : int) <= d ==> ~(d = (0 : int))) /\
           (!o2 : bool.
              (if (2 : int) <= d then
                 o2 =
                   (if n rem d = (0 : int) then T else F)
               else
                 o2 = F) ==>
              ~(o2 = T) ==>
              (let o3 = d + (1 : int)
               in
                 (((0 : int) <= n - d /\
                   n - o3 < n - d) /\
                  (2 : int) <= n /\
                  ((2 : int) <= o3 /\ o3 <= n) /\
                  (!i : int.
                     (2 : int) <= i /\ i < o3 ==>
                     ~lpf_divides i n))))) /\
         (!result : int.
            (if n < o1 then
               result = n
             else
               ?o2 : bool.
                 (if (2 : int) <= d then
                    o2 =
                      (if n rem d = (0 : int) then T else F)
                  else
                    o2 = F) /\
                 (if o2 = T then
                    result = d
                  else
                    (d + (1 : int) <= result /\ result <= n) /\
                    lpf_divides result n /\
                    (!i : int.
                       (2 : int) <= i /\ i < result ==>
                       ~lpf_divides i n))) ==>
            (d <= result /\ result <= n) /\
            lpf_divides result n /\
            (!i : int.
               (2 : int) <= i /\ i < result ==>
               ~lpf_divides i n))))``;
