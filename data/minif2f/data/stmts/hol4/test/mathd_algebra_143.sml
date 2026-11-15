(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_143: evaluating the
  composition of two pointwise-defined real functions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_143 =
  ``!f g : real -> real.
      (!x : real. f x = x + 1) /\
      (!x : real. g x = x pow 2 + 3)
      ==>
      f (g 2) = 8``;
