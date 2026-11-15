(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_149: the finite sum of the
  real preimages of 10 under a piecewise quadratic-linear function. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_sigmaTheory;

val mathd_algebra_149 =
  ``!f : real -> real.
      (!x : real. x < -5 ==> f x = x pow 2 + 5) /\
      (!x : real. -5 <= x ==> f x = 3 * x - 8) /\
      FINITE {x : real | f x = 10}
      ==>
      SIGMA (\x. x) {x : real | f x = 10} = 6``;
