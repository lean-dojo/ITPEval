(*
  Statement-only formalization of miniF2F test problem mathd_algebra_314: for the natural
  number n = 11, a real-valued identity involving powers of 1/4 and 2. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_314 =
  ``!n : num.
      n = 11
      ==>
      ((1 : real) / 4) pow (n + 1) *
        ((2 : real) pow (2 * n)) =
      (1 : real) / 4``;
