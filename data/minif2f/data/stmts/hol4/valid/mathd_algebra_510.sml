(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_510: a real-number identity
  for the square root of a sum of squares from a given sum and product. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_510 =
  ``!x y : real.
      x + y = 13 /\
      x * y = 24
      ==>
      sqrt (x pow 2 + y pow 2) = 11``;
