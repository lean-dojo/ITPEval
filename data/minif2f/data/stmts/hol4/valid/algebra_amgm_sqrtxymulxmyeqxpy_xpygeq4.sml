(*
  Statement-only formalization of miniF2F valid problem
  algebra_amgm_sqrtxymulxmyeqxpy_xpygeq4: positive real variables with y at most x satisfying
  a square-root product equation have sum at least four. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_amgm_sqrtxymulxmyeqxpy_xpygeq4 =
  ``!x y : real.
      0 < x /\
      0 < y /\
      y <= x /\
      sqrt (x * y) * (x - y) = x + y
      ==>
      x + y >= 4``;
