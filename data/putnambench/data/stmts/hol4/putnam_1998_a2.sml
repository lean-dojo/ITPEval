(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a2:
  for a first-quadrant arc of the unit circle, the sum of the areas below and
  to the left of the arc depends only on its arc length. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_1998_a2 =
  ``let quadrant =
      \P : real # real.
        0 < FST P /\ 0 < SND P /\
        FST P pow 2 + SND P pow 2 = 1
    in
    let isarc =
      \P Q : real # real.
        quadrant P /\ quadrant Q /\ FST Q < FST P
    in
    let arc =
      \P Q : real # real.
        {R : real # real |
          quadrant R /\ FST R < FST P /\ FST Q < FST R}
    in
    let A =
      \P Q : real # real.
        real
          (measure
            (prod_measure_space lebesgue lebesgue)
            {X : real # real |
              ?R : real # real.
                R IN arc P Q /\
                FST R = FST X /\
                SND X < SND R /\
                0 < SND X})
    in
    let B =
      \P Q : real # real.
        real
          (measure
            (prod_measure_space lebesgue lebesgue)
            {X : real # real |
              ?R : real # real.
                R IN arc P Q /\
                SND R = SND X /\
                FST X < FST R /\
                0 < FST X})
    in
      ?f : real -> real.
        !P Q : real # real.
          isarc P Q
          ==>
          A P Q + B P Q =
            f (atn (SND Q / FST Q) - atn (SND P / FST P))``;
