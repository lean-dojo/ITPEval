(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b3:
  a finite set of real-plane points whose every three-point triangle has area
  at most one is contained in a triangle of area four. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory;

val putnam_2016_b3 =
  ``!(S : (real # real) set).
      let convex_hull_three =
        \A B C : real # real.
          {P : real # real |
            ?u v w : real.
              0 <= u /\ 0 <= v /\ 0 <= w /\
              u + v + w = 1 /\
              P =
                (u * FST A + v * FST B + w * FST C,
                 u * SND A + v * SND B + w * SND C)}
      in
      let triangle_area =
        \A B C : real # real.
          abs ((FST B - FST A) * (SND C - SND A) -
               (SND B - SND A) * (FST C - FST A)) / 2
      in
        FINITE S /\
        (!A B C : real # real.
           A IN S /\ B IN S /\ C IN S
           ==>
           triangle_area A B C <= 1)
        ==>
        ?A1 B1 C1 : real # real.
          triangle_area A1 B1 C1 = 4 /\
          S SUBSET convex_hull_three A1 B1 C1``;
