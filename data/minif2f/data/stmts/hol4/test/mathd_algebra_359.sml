(*
  Statement-only formalization of miniF2F test problem mathd_algebra_359: solving a real linear
  equation for y. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_359 =
  ``!y : real.
      y + 6 + y = 2 * 12
      ==>
      y = 9``;
