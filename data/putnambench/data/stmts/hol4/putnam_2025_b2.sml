(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b2
  (putnambench__hol4__putnam_2025_b2): the x-coordinate of the centroid of
  the solid formed by rotating the region under a nonnegative, continuous,
  strictly increasing function on [0,1] exceeds that of the planar region.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory integrationTheory;

val putnam_2025_b2 =
  ``let unit_interval = interval [0, 1]
    in
      !f : real -> real.
        f continuous_on unit_interval /\
        (!x y : real.
           x IN unit_interval /\
           y IN unit_interval /\
           x < y
           ==>
           f x < f y) /\
        (!x : real.
           x IN unit_interval
           ==>
           0 <= f x)
        ==>
        integration$integral unit_interval
            (\x : real. x * f x) /
          integration$integral unit_interval f <
        integration$integral unit_interval
            (\x : real. x * f x pow 2) /
          integration$integral unit_interval
            (\x : real. f x pow 2)``;
