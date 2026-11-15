(*
  Statement-only formalization of miniF2F test problem mathd_algebra_44:
  solving a two-equation linear system over the reals determines s = 1 and
  t = 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_44 =
  ``!s t : real.
      s = 9 - 2 * t /\
      t = 3 * s + 1
      ==>
      s = 1 /\ t = 4``;
