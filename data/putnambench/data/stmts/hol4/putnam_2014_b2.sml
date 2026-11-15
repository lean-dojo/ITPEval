(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b2:
  the exact maximum ln(4/3) of the integral of f(x)/x on [1,3], where both
  integrands are integrable, f is bounded between -1 and 1, and its integral
  is zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_2014_b2 =
  ``let source_interval = interval [1, 3]
    in
    let admissible =
      \f : real -> real.
        f integrable_on source_interval /\
        (\x : real. f x / x) integrable_on source_interval /\
        (!x : real.
           x IN source_interval
           ==>
           ~1 <= f x /\ f x <= 1) /\
        integration$integral source_interval f = 0
    in
    let weighted_integral =
      \f : real -> real.
        integration$integral source_interval
          (\x : real. f x / x)
    in
    let solution = ln (4 / 3)
    in
      (?f : real -> real.
         admissible f /\
         weighted_integral f = solution) /\
      (!f : real -> real.
         admissible f
         ==>
         weighted_integral f <= solution)``;
