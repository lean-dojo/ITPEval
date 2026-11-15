(*
  Statement-only formalization of miniF2F valid problem imo_1966_p5: solving a
  four-equation absolute-distance system for weights on four strictly decreasing real
  values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val imo_1966_p5 =
  ``!x a : num -> real.
      a 1 <> a 2 /\
      a 1 <> a 3 /\
      a 1 <> a 4 /\
      a 2 <> a 3 /\
      a 2 <> a 4 /\
      a 3 <> a 4 /\
      a 1 > a 2 /\
      a 2 > a 3 /\
      a 3 > a 4 /\
      abs (a 1 - a 2) * x 2 +
          abs (a 1 - a 3) * x 3 +
          abs (a 1 - a 4) * x 4 = 1 /\
      abs (a 2 - a 1) * x 1 +
          abs (a 2 - a 3) * x 3 +
          abs (a 2 - a 4) * x 4 = 1 /\
      abs (a 3 - a 1) * x 1 +
          abs (a 3 - a 2) * x 2 +
          abs (a 3 - a 4) * x 4 = 1 /\
      abs (a 4 - a 1) * x 1 +
          abs (a 4 - a 2) * x 2 +
          abs (a 4 - a 3) * x 3 = 1
      ==>
      x 2 = 0 /\
      x 3 = 0 /\
      x 1 = 1 / abs (a 1 - a 4) /\
      x 4 = 1 / abs (a 1 - a 4)``;
