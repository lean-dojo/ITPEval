(*
  Statement-only formalization of miniF2F test problem
  algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1: a real absolute-value equation implying that
  the variable lies in the closed interval from 0 to 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 =
  ``!x : real.
      abs (x - 1) + abs x + abs (x + 1) = x + 2
      ==>
      0 <= x /\ x <= 1``;
