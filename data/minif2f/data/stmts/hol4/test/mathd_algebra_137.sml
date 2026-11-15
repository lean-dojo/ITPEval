(*
  Statement-only formalization of miniF2F test problem mathd_algebra_137. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val mathd_algebra_137 =
  ``!x : num.
      ((&x : real) + (4 : real) / 100 * &x = 598)
      ==>
      x = 575``;
