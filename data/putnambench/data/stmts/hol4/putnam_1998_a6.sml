(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a6:
  distinct integer-coordinate points whose stated distance and triangle-area
  inequality forces them to be three vertices of a square. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory realTheory intrealTheory
     transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_1998_a6 =
  ``let lattice_point =
      \P : real # real.
        ?x y : int.
          P = (real_of_int x, real_of_int y)
    in
    let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let convex_hull_three =
      \A B C : real # real.
        {X : real # real |
          ?u v w : real.
            0 <= u /\ 0 <= v /\ 0 <= w /\
            u + v + w = 1 /\
            X =
              (u * FST A + v * FST B + w * FST C,
               u * SND A + v * SND B + w * SND C)}
    in
    let triangle_area =
      \A B C : real # real.
        real
          (measure
            (prod_measure_space lebesgue lebesgue)
            (convex_hull_three A B C))
    in
    let threesquare =
      \P Q R : real # real.
        dist Q P = dist Q R /\
        (FST P - FST Q) * (FST R - FST Q) +
          (SND P - SND Q) * (SND R - SND Q) = 0
    in
      !A B C : real # real.
        lattice_point A /\
        lattice_point B /\
        lattice_point C /\
        A <> B /\ A <> C /\ B <> C /\
        (dist A B + dist B C) pow 2 <
          8 * triangle_area A B C + 1
        ==>
        threesquare A B C \/
        threesquare B C A \/
        threesquare C A B``;
