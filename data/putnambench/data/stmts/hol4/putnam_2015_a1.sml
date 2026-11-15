(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a1:
  a maximum-area triangle with vertices on the positive branch of xy = 1
  cuts off equal areas between the hyperbola and its two adjacent chords.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory integrationTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_2015_a1 =
  ``!(hyperbola : (real # real) set)
     (A B P : real # real)
     (PPline : (real # real) -> (real # real) -> real -> real).
      let convex_hull_three =
        \X Y Z : real # real.
          {Q : real # real |
            ?u v w : real.
              0 <= u /\ 0 <= v /\ 0 <= w /\
              u + v + w = 1 /\
              Q =
                (u * FST X + v * FST Y + w * FST Z,
                 u * SND X + v * SND Y + w * SND Z)}
      in
      let triangle_area =
        \X Y Z : real # real.
          measure
            (prod_measure_space lebesgue lebesgue)
            (convex_hull_three X Y Z)
      in
        hyperbola =
          {Q : real # real | SND Q = 1 / FST Q /\ 0 < FST Q} /\
        A IN hyperbola /\ B IN hyperbola /\ FST A < FST B /\
        P IN hyperbola /\ FST A < FST P /\ FST P < FST B /\
        (!Q : real # real.
           Q IN hyperbola /\ FST A < FST Q /\ FST Q < FST B
           ==>
           triangle_area A Q B <= triangle_area A P B) /\
        (!P1 P2 : real # real.
           FST P1 <> FST P2
           ==>
           PPline P1 P2 =
             (\x : real.
                (SND P2 - SND P1) / (FST P2 - FST P1) *
                  (x - FST P1) +
                SND P1))
        ==>
        integration$integral (interval [FST A, FST P])
          (\x : real. PPline A P x - 1 / x) =
        integration$integral (interval [FST P, FST B])
          (\x : real. PPline P B x - 1 / x)``;
