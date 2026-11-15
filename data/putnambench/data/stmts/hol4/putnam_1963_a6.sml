(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a6:
  three distinct chords of a real-plane ellipse, two passing through the
  midpoint of the third, determine two collinear intersections whose midpoint
  is the shared chord midpoint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;

val putnam_1963_a6 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let midpoint =
      \P Q : real # real.
        ((FST P + FST Q) / 2, (SND P + SND Q) / 2)
    in
    let collinear =
      \P Q R : real # real.
        (FST P - FST R) * (SND Q - SND R) =
        (SND P - SND R) * (FST Q - FST R)
    in
    let closed_segment =
      \A B : real # real.
      \X : real # real.
        ?t : real.
          0 <= t /\ t <= 1 /\
          X = ((1 - t) * FST A + t * FST B,
               (1 - t) * SND A + t * SND B)
    in
      !F1 F2 U V A B C D P Q M : real # real.
      !r : real. !E : (real # real) set.
        M = midpoint U V /\
        E = {H : real # real | dist F1 H + dist F2 H = r} /\
        r > dist F1 F2 /\
        U IN E /\ V IN E /\ U <> V /\
        A IN E /\ B IN E /\ A <> B /\
        C IN E /\ D IN E /\ C <> D /\
        A <> C /\ B <> D /\
        closed_segment A B <> closed_segment U V /\
        closed_segment C D <> closed_segment U V /\
        closed_segment A B <> closed_segment C D /\
        closed_segment A B M /\ closed_segment C D M /\
        collinear P A C /\ collinear P U V /\
        collinear Q B D /\ collinear Q U V
        ==>
        M = midpoint P Q``;
