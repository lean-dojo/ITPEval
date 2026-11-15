(*
  Statement-only formalization of miniF2F test problem mathd_algebra_171: evaluating the real
  affine function f(x) = 5x + 4 at x = 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_171 =
  ``!f : real -> real.
      (!x : real. f x = 5 * x + 4)
      ==>
      f 1 = 9``;
