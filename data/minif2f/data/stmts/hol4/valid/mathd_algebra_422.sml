(*
  Statement-only formalization of miniF2F artifact mathd_algebra_422: an affine real bijection
  whose value at x + 1 equals its inverse value at x determines x. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_422 =
  ``!x : real. !sigma inv_sigma : real -> real.
      (!t : real.
         sigma (inv_sigma t) = t /\
         inv_sigma (sigma t) = t) /\
      (!t : real. sigma t = 5 * t - 12) /\
      sigma (x + 1) = inv_sigma x
      ==>
      x = 47 / 24``;
