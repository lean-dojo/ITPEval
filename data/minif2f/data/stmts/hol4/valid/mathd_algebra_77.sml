(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_77: nonzero distinct real
  coefficients that are both roots of their quadratic determine the coefficients. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_77 =
  ``!a b : real. !f : real -> real.
      a <> 0 /\
      b <> 0 /\
      a <> b /\
      (!x : real. f x = x pow 2 + a * x + b) /\
      f a = 0 /\
      f b = 0
      ==>
      a = 1 /\ b = -2``;
