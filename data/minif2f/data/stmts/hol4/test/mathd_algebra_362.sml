(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_362: two nonlinear real
  equations involving powers and division determine a + b. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_362 =
  ``!a b : real.
      a pow 2 * b pow 3 = 32 / 27 /\
      a / (b pow 3) = 27 / 4
      ==>
      a + b = 8 / 3``;
