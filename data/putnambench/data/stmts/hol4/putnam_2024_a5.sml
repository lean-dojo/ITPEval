(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a5:
  the probability that a random chord of the radius-nine circle meets the
  unit disk centered at (r,0) is minimized on 0 <= r <= 8 exactly at r = 0.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_2024_a5 =
  ``let circle_point =
      \s : real.
        (9 * cos (2 * pi * s), 9 * sin (2 * pi * s))
    in
    let intersects =
      \r : real.
      \P Q : real # real.
        ?u : real.
          (FST P + u * (FST Q - FST P) - r) pow 2 +
            (SND P + u * (SND Q - SND P)) pow 2 = 1
    in
    let probability =
      \r : real.
        measure
          (prod_measure_space lebesgue lebesgue)
          {st : real # real |
             0 <= FST st /\ FST st <= 1 /\
             0 <= SND st /\ SND st <= 1 /\
             intersects r
               (circle_point (FST st))
               (circle_point (SND st))}
    in
      {r : real |
         0 <= r /\ r <= 8 /\
         !x : real.
           0 <= x /\ x <= 8 ==> probability r <= probability x} =
      {0}``;
