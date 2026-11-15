(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b1:
  the maximum number of rational-coordinate points on a circle in the real
  plane with a non-rational center is two. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_of_ratTheory
     transcTheory;

val putnam_2008_b1 =
  ``let rational_point =
      \P : real # real.
        FST P IN q_set /\ SND P IN q_set
    in
    let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let circle_points =
      \c : real # real. \r : real.
        {P : real # real |
           dist P c = r /\ rational_point P}
    in
      (?c : real # real. ?r : real.
         ~rational_point c /\ circle_points c r HAS_SIZE 2) /\
      (!c : real # real. !r : real.
         ~rational_point c
         ==>
         FINITE (circle_points c r) /\
         CARD (circle_points c r) <= 2)``;
