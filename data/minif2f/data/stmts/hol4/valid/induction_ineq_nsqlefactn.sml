(*
  Statement-only formalization of miniF2F valid problem induction_ineq_nsqlefactn: for every
  natural number n at least 4, n squared is at most n factorial. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val induction_ineq_nsqlefactn =
  ``!n : num. 4 <= n ==> n EXP 2 <= FACT n``;
