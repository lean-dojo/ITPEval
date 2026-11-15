(*
  Statement-only formalization of miniF2F test problem mathd_algebra_332. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_332 =
  ``!x y : real.
      (x + y) / 2 = 7 /\
      sqrt (x * y) = sqrt 19
      ==>
      x pow 2 + y pow 2 = 158``;
