(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_160: solving a two-equation
  linear system over the real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_160 =
  ``!n x : real.
      n + x = 97 /\
      n + 5 * x = 265
      ==>
      n + 2 * x = 139``;
