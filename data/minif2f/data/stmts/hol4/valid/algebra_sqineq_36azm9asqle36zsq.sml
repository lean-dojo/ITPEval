(*
  Statement-only formalization of miniF2F valid problem algebra_sqineq_36azm9asqle36zsq: a
  quadratic inequality over arbitrary real variables. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_sqineq_36azm9asqle36zsq =
  ``!z a : real.
      36 * (a * z) - 9 * a pow 2 <= 36 * z pow 2``;
