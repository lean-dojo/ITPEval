(*
  Statement-only formalization of miniF2F artifact mathd_algebra_156: two real polynomial
  functions intersect at x and y, and the ordered squares differ by one. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_156 =
  ``!x y : real. !f g : real -> real.
      (!t : real. f t = t pow 4) /\
      (!t : real. g t = 5 * t pow 2 - 6) /\
      f x = g x /\
      f y = g y /\
      x pow 2 < y pow 2
      ==>
      y pow 2 - x pow 2 = 1``;
