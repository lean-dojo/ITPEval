(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_151: the integer ceiling
  of sqrt 27 minus the integer floor of sqrt 26 equals one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val mathd_algebra_151 =
  ``INT_CEILING (sqrt (27 : real)) -
    INT_FLOOR (sqrt (26 : real)) = (1 : int)``;
