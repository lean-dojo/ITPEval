(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_547: for real x and y
  fixed as 5 and 2, the square root of x cubed minus 2 raised to y is 11. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_547 =
  ``!x y : real.
      x = 5 /\
      y = 2
      ==>
      sqrt (x pow 3 - (2 : real) powr y) = 11``;
