(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a5:
  the maximum over the closed unit interval of the integral from zero to y
  of sqrt(x^4 + (y - y^2)^2) is 1/3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_1991_a5 =
  ``let f =
      \y : real.
        integration$integral (interval [0, y])
          (\x : real. sqrt (x pow 4 + (y - y pow 2) pow 2))
    in
    let solution = (1 / 3 : real)
    in
      (!y : real.
         0 <= y /\ y <= 1
         ==>
         f y <= solution) /\
      (?y : real.
         0 <= y /\ y <= 1 /\
         f y = solution)``;
