(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_616: evaluating at 1 the
  composition of the real functions f(x) = x^3 + 2*x + 1 and g(x) = x - 1. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_616 =
  ``!f g : real -> real.
      (!x : real. f x = x pow 3 + 2 * x + 1) /\
      (!x : real. g x = x - 1)
      ==>
      f (g 1) = 1``;
