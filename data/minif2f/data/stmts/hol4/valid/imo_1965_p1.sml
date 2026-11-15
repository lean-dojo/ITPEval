(*
  Statement-only formalization of miniF2F valid problem imo_1965_p1: a trigonometric
  inequality on a real variable in [0, 2 pi] implying that it lies in
  [pi / 4, 7 pi / 4]. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val imo_1965_p1 =
  ``!x : real.
      0 <= x /\
      x <= 2 * pi /\
      2 * cos x <=
        abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) /\
      abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) <= sqrt 2
      ==>
      pi / 4 <= x /\ x <= 7 * pi / 4``;
