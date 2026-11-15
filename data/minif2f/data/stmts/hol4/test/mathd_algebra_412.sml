(*
  Statement-only formalization of miniF2F test problem mathd_algebra_412: two real linear
  equations imply x = 18. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_412 =
  ``!x y : real.
      x + y = 25 /\
      x - y = 11
      ==>
      x = 18``;
