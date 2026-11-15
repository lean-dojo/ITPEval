(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a1:
  the equal-area horizontal line for the first-quadrant cubic
  y = 2x - 3x^3 has height 4/9. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_1993_a1 =
  ``let solution = (4 / 9 : real)
    in
      0 < solution /\
      solution < 4 * sqrt 2 / 9 /\
      integration$integral (interval [0, sqrt 2 / 3])
        (\x : real.
           max (solution - (2 * x - 3 * x pow 3)) 0) =
      integration$integral (interval [0, sqrt 6 / 3])
        (\x : real.
           max ((2 * x - 3 * x pow 3) - solution) 0)``;
