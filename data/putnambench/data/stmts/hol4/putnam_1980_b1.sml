(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1980_b1:
  the real constants c for which the hyperbolic-cosine exponential inequality
  holds for every real x are exactly those at least one half. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_1980_b1 =
  ``!c : real.
      ((!x : real.
          (exp x + exp (-x)) / 2 <= exp (c * x pow 2))
       <=>
       (1 / 2 : real) <= c)``;
