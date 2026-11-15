(*
  Statement-only formalization of miniF2F test problem mathd_algebra_346: evaluating a
  composition of two specified real affine functions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_346 =
  ``!f g : real -> real.
      (!x : real. f x = 2 * x - 3) /\
      (!x : real. g x = x + 1)
      ==>
      g (f 5 - 1) = 7``;
