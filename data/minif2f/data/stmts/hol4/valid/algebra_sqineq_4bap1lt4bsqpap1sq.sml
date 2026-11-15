(*
  Statement-only formalization of miniF2F valid problem
  algebra_sqineq_4bap1lt4bsqpap1sq: a universal quadratic inequality in two real variables.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_sqineq_4bap1lt4bsqpap1sq =
  ``!a b : real.
      4 * b * (a + 1) <= 4 * b pow 2 + (a + 1) pow 2``;
