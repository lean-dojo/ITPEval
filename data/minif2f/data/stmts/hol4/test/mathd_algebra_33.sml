(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_33: real proportionality
  equations determine the ratio z / x. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val mathd_algebra_33 =
  ``!x y z : real.
      ~(x = 0) /\
      2 * x = 5 * y /\
      7 * y = 10 * z
      ==>
      z / x = 7 / 25``;

val _ = export_theory();
