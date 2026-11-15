(*
  Statement-only formalization of miniF2F artifact mathd_algebra_141: real numbers with product
  180 and twice their sum 54 have sum of squares 369. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_141 =
  ``!a b : real.
      a * b = 180 /\
      2 * (a + b) = 54
      ==>
      a pow 2 + b pow 2 = 369``;
