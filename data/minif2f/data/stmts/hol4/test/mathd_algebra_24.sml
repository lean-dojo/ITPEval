(*
  Statement-only formalization of miniF2F test problem mathd_algebra_24:
  solving a real linear equation involving division by 50. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_24 =
  ``!x : real.
      x / 50 = 40
      ==>
      x = 2000``;
