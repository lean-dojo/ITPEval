(*
  Statement-only formalization of miniF2F test problem mathd_algebra_354: two real linear
  equations determine the value of a + 20 * d. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_354 =
  ``!a d : real.
      a + 6 * d = 30 /\
      a + 10 * d = 60
      ==>
      a + 20 * d = 135``;
