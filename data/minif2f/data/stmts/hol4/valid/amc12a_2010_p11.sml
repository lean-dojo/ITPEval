(*
  Statement-only formalization of miniF2F valid problem amc12a_2010_p11: an exponential and
  logarithmic system determining the real base b. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val amc12a_2010_p11 =
  ``!x b : real.
      0 < b /\
      7 powr (x + 7) = 8 powr x /\
      x = logr b (7 pow 7)
      ==>
      b = 8 / 7``;
