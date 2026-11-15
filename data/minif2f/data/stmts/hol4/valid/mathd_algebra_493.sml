(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_493: the value of f(f(4))
  for the real function f(x) = x^2 - 4 * sqrt(x) + 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_493 =
  ``!f : real -> real.
      (!x : real. f x = x pow 2 - 4 * sqrt x + 1)
      ==>
      f (f 4) = 70``;
