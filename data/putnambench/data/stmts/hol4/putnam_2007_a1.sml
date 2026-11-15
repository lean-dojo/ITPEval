(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a1:
  the real parameters for which the two mutually defined quadratic curves are
  tangent are exactly four explicit values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory real_topologyTheory limTheory transcTheory derivativeTheory;

val putnam_2007_a1 =
  ``let deriv0 =
      \f : real -> real.
        \x : real.
          if f differentiable (at x) then vector_derivative f (at x) else 0
    in
      !(P : (real -> real) -> bool) (a : real).
        (!f : real -> real.
           P f <=>
           ?x y : real.
             f x = y /\
             f y = x /\
             deriv0 f x * deriv0 f y = 1)
        ==>
        (P (\t : real. a * t pow 2 + a * t + 1 / 24) <=>
         a = 2 / 3 \/
         a = 3 / 2 \/
         a = (13 + sqrt 601) / 12 \/
         a = (13 - sqrt 601) / 12)``;
