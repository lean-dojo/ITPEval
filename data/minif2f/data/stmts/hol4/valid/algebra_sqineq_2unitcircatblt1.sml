(*
  Statement-only formalization of miniF2F valid artifact algebra_sqineq_2unitcircatblt1:
  real numbers whose squares sum to 2 have product at most 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_sqineq_2unitcircatblt1 =
  ``!a b : real.
      a pow 2 + b pow 2 = 2
      ==>
      a * b <= 1``;
