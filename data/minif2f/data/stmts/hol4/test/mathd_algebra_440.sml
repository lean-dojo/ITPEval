(*
  Statement-only formalization of miniF2F test problem mathd_algebra_440: a real linear equation
  determines x to be 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val mathd_algebra_440 =
  ``!x : real.
      3 / 2 / 3 = x / 10
      ==>
      x = 5``;

val _ = export_theory();
