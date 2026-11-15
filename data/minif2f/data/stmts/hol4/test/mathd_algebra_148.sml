(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_148:
  determining the coefficient of a real cubic function from its value at 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_148 =
  ``!c : real. !f : real -> real.
      (!x : real. f x = c * x pow 3 - 9 * x + 3) /\
      f 2 = 9
      ==>
      c = 3``;
