(*
  Statement-only formalization of miniF2F valid problem
  algebra_2rootsintpoly_am10tap11eqasqpam110: the factored and expanded forms of a
  quadratic polynomial agree for every complex number a. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val algebra_2rootsintpoly_am10tap11eqasqpam110 =
  ``!a : complex.
      (a - 10) * (a + 11) = a pow 2 + a - 110``;
