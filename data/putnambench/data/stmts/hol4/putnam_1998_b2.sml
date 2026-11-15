(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b2:
  the minimum perimeter of a nondegenerate triangle with one fixed vertex,
  one vertex on the x-axis, and one on the line y = x. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1998_b2 =
  ``!a b : real.
      0 < b /\ b < a
      ==>
      let dist =
        \P Q : real # real.
          sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
      in
      let perimeter =
        \c x : real.
          dist (a, b) (c, 0) +
          dist (c, 0) (x, x) +
          dist (a, b) (x, x)
      in
      let valid_triangle =
        \c x : real.
          dist (a, b) (c, 0) + dist (c, 0) (x, x) >
            dist (a, b) (x, x) /\
          dist (a, b) (c, 0) + dist (a, b) (x, x) >
            dist (c, 0) (x, x) /\
          dist (c, 0) (x, x) + dist (a, b) (x, x) >
            dist (a, b) (c, 0)
      in
      let solution = sqrt (2 * a pow 2 + 2 * b pow 2)
      in
        (!c x : real.
           valid_triangle c x ==> solution <= perimeter c x) /\
        (?c x : real.
           valid_triangle c x /\ perimeter c x = solution)``;
