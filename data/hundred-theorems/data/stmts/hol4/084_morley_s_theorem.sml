(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__084, cataloged as "Morley's Theorem": the adjacent
  internal angle trisectors of a nondegenerate real-plane triangle determine
  three points forming an equilateral triangle. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val morleys_theorem =
  ``let collinear =
      \P Q R : real # real.
        (FST P - FST Q) * (SND R - SND Q) =
        (SND P - SND Q) * (FST R - FST Q)
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
    let in_triangle =
      \X A B C : real # real.
        ?u v w : real.
          0 <= u /\ 0 <= v /\ 0 <= w /\ u + v + w = 1 /\
          X = (u * FST A + v * FST B + w * FST C,
               u * SND A + v * SND B + w * SND C)
    in
      !A B C P Q R : real # real.
        ~collinear A B C /\
        in_triangle P A B C /\
        in_triangle Q A B C /\
        in_triangle R A B C /\
        angle A B R = angle A B C / 3 /\
        angle B A R = angle B A C / 3 /\
        angle B C P = angle B C A / 3 /\
        angle C B P = angle C B A / 3 /\
        angle C A Q = angle C A B / 3 /\
        angle A C Q = angle A C B / 3
        ==>
        dist R P = dist P Q /\ dist Q R = dist P Q``;
