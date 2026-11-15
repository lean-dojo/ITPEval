(*
  Statement-only formalization of miniF2F valid problem amc12a_2008_p8: positive real variables
  satisfying cubic and quadratic equations, with a square-root conclusion. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12a_2008_p8 =
  ``!x y : real.
      0 < x /\
      0 < y /\
      y pow 3 = 1 /\
      6 * x pow 2 = 2 * (6 * y pow 2)
      ==>
      x pow 3 = 2 * sqrt 2``;
