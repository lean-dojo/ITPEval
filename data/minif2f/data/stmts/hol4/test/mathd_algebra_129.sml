(*
  Statement-only formalization of miniF2F artifact mathd_algebra_129: solving a reciprocal
  equation over the real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_129 =
  ``!a : real.
      ~(a = 0) /\
      ((1 : real) / 8) / ((1 : real) / 4) - 1 / a = 1
      ==>
      a = -2``;
