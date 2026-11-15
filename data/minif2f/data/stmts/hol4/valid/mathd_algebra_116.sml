(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_116: determining the
  constant in a quadratic equation from a specified radical root. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_116 =
  ``!k x : real.
      x = (13 - sqrt 131) / 4 /\
      2 * x pow 2 - 13 * x + k = 0
      ==>
      k = 19 / 4``;
