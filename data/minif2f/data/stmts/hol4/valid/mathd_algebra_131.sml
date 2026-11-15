(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_131: a reciprocal identity
  for the distinct real roots of a quadratic. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_131 =
  ``!a b : real. !f : real -> real.
      (!x : real. f x = 2 * x pow 2 - 7 * x + 2) /\
      f a = 0 /\
      f b = 0 /\
      a <> b
      ==>
      1 / (a - 1) + 1 / (b - 1) = -1``;
