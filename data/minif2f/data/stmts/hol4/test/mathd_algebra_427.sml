(*
  Statement-only formalization of miniF2F test problem mathd_algebra_427: three real linear
  equations imply the sum of the variables. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_427 =
  ``!x y z : real.
      3 * x + y = 17 /\
      5 * y + z = 14 /\
      3 * x + 5 * z = 41
      ==>
      x + y + z = 12``;
