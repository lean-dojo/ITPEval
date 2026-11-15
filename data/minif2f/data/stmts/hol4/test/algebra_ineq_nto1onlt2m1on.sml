(*
  Statement-only formalization of miniF2F test problem algebra_ineq_nto1onlt2m1on:
  the real n-th-root inequality n^(1/n) <= 2 - 1/n for every natural number n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val algebra_ineq_nto1onlt2m1on =
  ``!n : num.
      (&n : real) powr (1 / &n) <= 2 - 1 / &n``;
