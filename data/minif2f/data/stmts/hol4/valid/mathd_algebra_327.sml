(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_327: an absolute-value
  inequality over a real variable implies that it lies strictly between -7 and -2. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_327 =
  ``!a : real.
      1 / 5 * abs (9 + 2 * a) < 1
      ==>
      -7 < a /\ a < -2``;
