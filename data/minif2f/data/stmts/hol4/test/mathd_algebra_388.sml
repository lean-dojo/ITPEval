(*
  Statement-only formalization of miniF2F test problem mathd_algebra_388: solving for one
  variable in a real linear system. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_388 =
  ``!x y z : real.
      3 * x + 4 * y - 12 * z = 10 /\
      (-2) * x - 3 * y + 9 * z = -4
      ==>
      x = 14``;
