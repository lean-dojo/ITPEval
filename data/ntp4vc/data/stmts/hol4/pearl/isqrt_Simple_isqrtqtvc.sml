(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/isqrt_Simple_isqrtqtvc: the integer-square-root simple-loop
  verification condition, including initialization, variant decrease, loop
  preservation, and the terminal square-root specification. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val isqrt_Simple_isqrtqtvc_statement =
  ``let sqr =
      \z : int. z * z
    in
    let isqrt_spec =
      \z : int. \res : int.
        (0 : int) <= res /\
        sqr res <= z /\
        z < sqr (res + (1 : int))
    in
      !x : int.
        (0 : int) <= x
        ==>
        (0 : int) <= (0 : int) /\
        sqr (0 : int) <= x /\
        (1 : int) = sqr ((0 : int) + (1 : int)) /\
        (!count : int.
           (0 : int) <= count /\ sqr count <= x
           ==>
           if sqr (count + (1 : int)) <= x then
             ((0 : int) <= x - count /\
              x - (count + (1 : int)) < x - count) /\
             (0 : int) <= count + (1 : int) /\
             sqr (count + (1 : int)) <= x /\
             sqr (count + (1 : int)) +
                 ((2 : int) * (count + (1 : int)) + (1 : int)) =
               sqr (count + (1 : int) + (1 : int))
           else
             isqrt_spec x count)``;
