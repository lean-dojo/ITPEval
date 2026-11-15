(*
  Statement-only formalization of "The Triangle Inequality" from Hundred Theorems
  item 091: the absolute value of a sum of two real numbers is at most the sum
  of their absolute values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val the_triangle_inequality =
  ``!x y : real. abs (x + y) <= abs x + abs y``;
