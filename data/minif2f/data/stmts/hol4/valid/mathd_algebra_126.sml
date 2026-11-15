(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_126, concerning two real
  linear equations that imply x = 15 and y = -11. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_126 =
  ``!x y : real.
      2 * 3 = x - 9 /\
      2 * (-5) = y + 1
      ==>
      x = 15 /\ y = -11``;
