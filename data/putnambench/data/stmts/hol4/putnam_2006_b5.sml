(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b5:
  the maximum of the difference between two weighted integrals associated
  with a continuous real function on the unit interval is 1/16. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory integrationTheory;

val putnam_2006_b5 =
  ``let unit_interval = interval [0, 1]
    in
    let I =
      \f : real -> real.
        integration$integral unit_interval
          (\x : real. x pow 2 * f x)
    in
    let J =
      \f : real -> real.
        integration$integral unit_interval
          (\x : real. x * f x pow 2)
    in
    let solution = (1 / 16 : real)
    in
      (?f : real -> real.
         f continuous_on unit_interval /\
         I f - J f = solution) /\
      (!f : real -> real.
         f continuous_on unit_interval
         ==>
         I f - J f <= solution)``;
