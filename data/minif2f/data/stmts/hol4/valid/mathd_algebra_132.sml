(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_132: commuting the real
  functions x + 2 and x squared determines the input. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_132 =
  ``!x : real. !f g : real -> real.
      (!t : real. f t = t + 2) /\
      (!t : real. g t = t pow 2) /\
      f (g x) = g (f x)
      ==>
      x = -1 / 2``;
