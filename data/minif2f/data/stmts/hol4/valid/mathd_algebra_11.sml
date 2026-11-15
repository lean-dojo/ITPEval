(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_11: a rational-expression
  identity over the real numbers under nonzero-denominator assumptions. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val mathd_algebra_11 =
  ``!a b : real.
      a <> b /\
      a <> 2 * b /\
      (4 * a + 3 * b) / (a - 2 * b) = 5
      ==>
      (a + 11 * b) / (a - b) = 2``;

val _ = export_theory();
