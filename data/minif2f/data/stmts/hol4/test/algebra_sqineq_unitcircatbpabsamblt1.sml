(*
  Statement-only formalization of miniF2F test artifact
  algebra_sqineq_unitcircatbpabsamblt1: a real unit-circle constraint implies
  an upper bound for a product plus an absolute difference. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val algebra_sqineq_unitcircatbpabsamblt1 =
  ``!a b : real.
      a pow 2 + b pow 2 = 1
      ==>
      a * b + abs (a - b) <= 1``;
