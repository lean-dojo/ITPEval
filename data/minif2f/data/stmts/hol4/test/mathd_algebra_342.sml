(*
  Statement-only formalization of miniF2F artifact mathd_algebra_342: two finite sums from a
  real arithmetic progression determine its initial term. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val mathd_algebra_342 =
  ``!a d : real.
      SIGMA (\k. a + &k * d) (count 5) = 70 /\
      SIGMA (\k. a + &k * d) (count 10) = 210
      ==>
      a = 42 / 5``;
