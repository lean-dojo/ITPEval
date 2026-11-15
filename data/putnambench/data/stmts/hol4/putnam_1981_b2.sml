(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_b2:
  the minimum of a four-term sum of squared successive ratio deviations over
  real numbers satisfying 1 <= r <= s <= t <= 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_1981_b2 =
  ``let feasible =
      \r s t : real.
        1 <= r /\ r <= s /\ s <= t /\ t <= 4
    in
    let objective =
      \r s t : real.
        (r - 1) pow 2 +
        (s / r - 1) pow 2 +
        (t / s - 1) pow 2 +
        (4 / t - 1) pow 2
    in
    let solution = 12 - 8 * sqrt 2
    in
      (!r s t : real.
         feasible r s t ==> solution <= objective r s t) /\
      (?r s t : real.
         feasible r s t /\ solution = objective r s t)``;
