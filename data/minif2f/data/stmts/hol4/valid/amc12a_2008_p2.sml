(*
  Statement-only formalization of miniF2F valid problem amc12a_2008_p2: solving a real linear
  equation with fractional coefficients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12a_2008_p2 =
  ``!x : real.
      x * (1 / 2 + 2 / 3) = 1
      ==>
      x = 6 / 7``;
