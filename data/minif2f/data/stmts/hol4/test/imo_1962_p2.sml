(*
  Statement-only formalization of miniF2F test problem imo_1962_p2: a radical
  inequality constrains a real variable to an explicit interval. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val imo_1962_p2 =
  ``!x : real.
      0 <= 3 - x /\
      0 <= x + 1 /\
      1 / 2 < sqrt (3 - x) - sqrt (x + 1)
      ==>
      ~1 <= x /\ x < 1 - sqrt 31 / 8``;
