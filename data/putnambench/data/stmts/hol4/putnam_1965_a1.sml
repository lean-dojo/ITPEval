(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a1:
  in a nondegenerate real-plane triangle with the prescribed angle ordering,
  two external-angle-bisector intersections at equal distances force angle
  CAB to equal pi / 15. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1965_a1 =
  ``let collinear =
      \P Q R : real # real.
        (FST P - FST R) * (SND Q - SND R) =
        (SND P - SND R) * (FST Q - FST R)
    in
    let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let angle =
      \P Q R : real # real.
        if P = Q \/ R = Q then
          pi / 2
        else
          acs
            (((FST P - FST Q) * (FST R - FST Q) +
               (SND P - SND Q) * (SND R - SND Q)) /
             (dist P Q * dist R Q))
    in
      !A B C X Y : real # real.
        ~collinear A B C /\
        angle C A B < angle B C A /\
        angle B C A < pi / 2 /\
        pi / 2 < angle A B C /\
        collinear X B C /\
        angle X A B = (pi - angle C A B) / 2 /\
        dist A X = dist A B /\
        collinear Y C A /\
        angle Y B C = (pi - angle A B C) / 2 /\
        dist B Y = dist A B
        ==>
        angle C A B = pi / 15``;
