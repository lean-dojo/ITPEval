(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_104: solving a linear
  proportion over the real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_104 =
  ``!x : real.
      125 / 8 = x / 12
      ==>
      x = 375 / 2``;
