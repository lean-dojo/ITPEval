(*
  Statement-only formalization of miniF2F valid problem
  algebra_binomnegdiscrineq_10alt28asqp1: a universal quadratic inequality in one real
  variable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_binomnegdiscrineq_10alt28asqp1 =
  ``!a : real.
      10 * a <= 28 * a pow 2 + 1``;
