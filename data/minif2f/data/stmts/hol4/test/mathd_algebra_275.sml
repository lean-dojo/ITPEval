(*
  Statement-only formalization of miniF2F test problem mathd_algebra_275: a real-exponentiation
  implication relating two powers of the positive fourth root of 11. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_275 =
  ``!x : real.
      (11 powr (1 / 4 : real)) powr (3 * x - 3) = 1 / 5
      ==>
      (11 powr (1 / 4 : real)) powr (6 * x + 2) = 121 / 25``;
