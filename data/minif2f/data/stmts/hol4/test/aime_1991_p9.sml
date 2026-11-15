(*
  Statement-only formalization of miniF2F test problem aime_1991_p9: trigonometric equations
  determine a rational whose reduced numerator and denominator sum to 44. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory transcTheory ratTheory
     real_of_ratTheory;

val aime_1991_p9 =
  ``!x : real. !m : rat.
      1 / cos x + tan x = 22 / 7 /\
      1 / sin x + 1 / tan x = real_of_rat m
      ==>
      RATN m + &(RATD m) = 44``;
