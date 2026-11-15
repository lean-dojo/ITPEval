(*
  Statement-only formalization of miniF2F test problem mathd_algebra_398: a proportionality
  identity for three positive real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val mathd_algebra_398 =
  ``!a b c : real.
      0 < a /\ 0 < b /\ 0 < c /\
      9 * b = 20 * c /\
      7 * a = 4 * b
      ==>
      63 * a = 80 * c``;

val _ = export_theory();
