(*
  Statement-only formalization of miniF2F valid problem aimeI_2000_p7: positive real reciprocal
  equations determine a positive rational whose reduced numerator and denominator sum to 5.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory ratTheory real_of_ratTheory;

val aimeI_2000_p7 =
  ``!x y z : real. !m : rat.
      0 < x /\ 0 < y /\ 0 < z /\
      x * y * z = 1 /\
      x + 1 / z = 5 /\
      y + 1 / x = 29 /\
      z + 1 / y = real_of_rat m /\
      0 < m
      ==>
      &(RATD m) + RATN m = 5``;
