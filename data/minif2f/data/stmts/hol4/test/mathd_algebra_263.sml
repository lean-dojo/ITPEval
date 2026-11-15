(*
  Statement-only formalization of miniF2F test problem mathd_algebra_263: solving a real
  square-root equation under its nonnegativity condition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_263 =
  ``!y : real.
      0 <= 19 + 3 * y /\
      sqrt (19 + 3 * y) = 7
      ==>
      y = 10``;
