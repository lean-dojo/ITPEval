(*
  Statement-only formalization of miniF2F test problem algebra_sqineq_at2malt1: the quadratic
  inequality a * (2 - a) <= 1 for every real a. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val algebra_sqineq_at2malt1 =
  ``!a : real. a * (2 - a) <= 1``;
