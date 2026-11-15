(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a3:
  a real function satisfying the stated arctangent functional equation has
  definite integral 3*pi/8 on the unit interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_2016_a3 =
  ``!f : real -> real.
      (!x : real.
         x <> 0
         ==>
         f x + f (1 - 1 / x) = atn x)
      ==>
      integration$integral (interval [0, 1]) f = 3 * pi / 8``;
