(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b1:
  the area probability that a point in the unit square is closer to its center
  than to every boundary point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory pairTheory pred_setTheory;
open realTheory intrealTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_1989_b1 =
  ``let sqdist =
      \P Q : real # real.
        (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2
    in
    let dist =
      \P Q : real # real. sqrt (sqdist P Q)
    in
    let square =
      {P : real # real |
        0 <= FST P /\ FST P <= 1 /\
        0 <= SND P /\ SND P <= 1}
    in
    let edges =
      {P : real # real |
        P IN square /\
        (FST P = 0 \/ FST P = 1 \/
         SND P = 0 \/ SND P = 1)}
    in
    let center = (1 / 2, 1 / 2) : real # real
    in
    let Scloser =
      {P : real # real |
        P IN square /\
        !Q : real # real.
          Q IN edges ==> dist P center < dist P Q}
    in
    let area = measure (prod_measure_space lebesgue lebesgue)
    in
      area Scloser / area square =
        Normal ((4 * sqrt 2 - 5) / 3)``;
