(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1980_b5:
  classification of the nonnegative parameters for which the nonnegative,
  strictly increasing, convex continuous functions on the unit interval
  satisfying the specified three-point inequality are closed under pointwise
  multiplication. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory;

val putnam_1980_b5 =
  ``let unit_interval = interval [0, 1]
    in
    let is_convex =
      \f : real -> real.
        !u v s : real.
          u IN unit_interval /\
          v IN unit_interval /\
          s IN unit_interval
          ==>
          f (s * u + (1 - s) * v) <=
          s * f u + (1 - s) * f v
    in
    let in_S =
      \t : real.
      \f : real -> real.
        (!x : real. x IN unit_interval ==> 0 <= f x) /\
        (!x y : real.
           x IN unit_interval /\
           y IN unit_interval /\
           x < y
           ==>
           f x < f y) /\
        is_convex f /\
        f continuous_on unit_interval /\
        f 1 - 2 * f (2 / 3) + f (1 / 3) >=
          t * (f (2 / 3) - 2 * f (1 / 3) + f 0)
    in
      !t : real.
        0 <= t
        ==>
        ((!f g : real -> real.
            in_S t f /\ in_S t g
            ==>
            in_S t (\x : real. f x * g x))
         <=>
         t <= 1)``;
