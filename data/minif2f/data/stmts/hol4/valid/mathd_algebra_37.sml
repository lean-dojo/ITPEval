(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_37: deriving a difference
  of squares from a two-variable linear system over the reals. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_37 =
  ``!x y : real.
      x + y = 7 /\
      3 * x + y = 45
      ==>
      x pow 2 - y pow 2 = 217``;
