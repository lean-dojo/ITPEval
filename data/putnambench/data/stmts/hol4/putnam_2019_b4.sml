(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b4:
  the common minimum of a four-point difference for twice continuously
  differentiable real functions satisfying two specified partial differential
  equations on the quadrant x,y >= 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory transcTheory;

val putnam_2019_b4 =
  ``let partial_x =
      \f : real -> real -> real.
      \x y : real.
        diffn 1 (\u : real. f u y) x
    in
    let partial_y =
      \f : real -> real -> real.
      \x y : real.
        diffn 1 (f x) y
    in
    let partial_xx =
      \f : real -> real -> real.
      \x y : real.
        diffn 2 (\u : real. f u y) x
    in
    let partial_xy =
      \f : real -> real -> real.
      \x y : real.
        diffn 1 (\v : real. partial_x f x v) y
    in
    let partial_yx =
      \f : real -> real -> real.
      \x y : real.
        diffn 1 (\u : real. partial_y f u y) x
    in
    let partial_yy =
      \f : real -> real -> real.
      \x y : real.
        diffn 2 (f x) y
    in
    let continuous_on_quadrant =
      \h : real -> real -> real.
        !u v e : real.
          1 <= u /\ 1 <= v /\ 0 < e
          ==>
          ?d : real.
            0 < d /\
            !x y : real.
              1 <= x /\ 1 <= y /\
              (x - u) pow 2 + (y - v) pow 2 < d
              ==>
              abs (h x y - h u v) < e
    in
    let twice_continuously_differentiable =
      \f : real -> real -> real.
        (!x y : real.
           1 <= x /\ 1 <= y
           ==>
           higher_differentiable 2 (\u : real. f u y) x /\
           higher_differentiable 2 (f x) y /\
           higher_differentiable
             1
             (\v : real. partial_x f x v)
             y /\
           higher_differentiable
             1
             (\u : real. partial_y f u y)
             x) /\
        continuous_on_quadrant (partial_x f) /\
        continuous_on_quadrant (partial_y f) /\
        continuous_on_quadrant (partial_xx f) /\
        continuous_on_quadrant (partial_xy f) /\
        continuous_on_quadrant (partial_yx f) /\
        continuous_on_quadrant (partial_yy f)
    in
    let four_point_difference =
      \f : real -> real -> real.
      \s : real.
        f (s + 1) (s + 1) -
        f (s + 1) s -
        f s (s + 1) +
        f s s
    in
    let solution = (2 * ln 2 - 1 / 2 : real)
    in
      !f : real -> real -> real.
        twice_continuously_differentiable f /\
        (!x y : real.
           1 <= x /\ 1 <= y
           ==>
           x * partial_x f x y + y * partial_y f x y =
             x * y * ln (x * y)) /\
        (!x y : real.
           1 <= x /\ 1 <= y
           ==>
           x pow 2 * partial_xx f x y +
             y pow 2 * partial_yy f x y =
             x * y)
        ==>
        (!s : real.
           1 <= s
           ==>
           solution <= four_point_difference f s) /\
        (?s : real.
           1 <= s /\
           four_point_difference f s = solution)``;
