(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a1:
  among five real-plane points with no three collinear, four form the vertices
  of a convex quadrilateral. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory;

val putnam_1962_a1 =
  ``let collinear =
      \P Q R : real # real.
        (FST P - FST R) * (SND Q - SND R) =
        (SND P - SND R) * (FST Q - FST R)
    in
    let in_convex_hull_of_three =
      \X (U : (real # real) set).
        ?P Q R : real # real.
          (!Y : real # real.
             Y IN U <=> Y = P \/ Y = Q \/ Y = R) /\
          ?a b c : real.
            0 <= a /\ 0 <= b /\ 0 <= c /\ a + b + c = 1 /\
            X = (a * FST P + b * FST Q + c * FST R,
                 a * SND P + b * SND Q + c * SND R)
    in
      !(S : (real # real) set).
        FINITE S /\
        CARD S = 5 /\
        (!P Q R : real # real.
           P IN S /\ Q IN S /\ R IN S /\
           P <> Q /\ P <> R /\ Q <> R
           ==>
           ~collinear P Q R)
        ==>
        ?T : (real # real) set.
          T SUBSET S /\
          FINITE T /\
          CARD T = 4 /\
          ~(?t : real # real.
              t IN T /\ in_convex_hull_of_three t (T DELETE t))``;
