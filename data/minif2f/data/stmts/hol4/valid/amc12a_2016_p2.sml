(*
  Statement-only formalization of miniF2F valid problem amc12a_2016_p2. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val amc12a_2016_p2 =
  ``!x : real.
      10 powr x * 100 powr (2 * x) = 1000 pow 5
      ==>
      x = 3``;
