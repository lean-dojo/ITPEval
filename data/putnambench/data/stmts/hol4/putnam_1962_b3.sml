(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b3:
  boundedness of a convex plane set that contains the origin and omits a
  point on every ray, under an interior-point or closedness assumption.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory;

val putnam_1962_b3 =
  ``!(S : (real # real) set).
      let sqdist =
        \P Q : real # real.
          (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2
      in
      let convex_plane =
        \T : (real # real) set.
          !P Q : real # real. !u : real.
            P IN T /\ Q IN T /\ 0 <= u /\ u <= 1
            ==>
            ((1 - u) * FST P + u * FST Q,
             (1 - u) * SND P + u * SND Q) IN T
      in
      let origin_interior =
        \T : (real # real) set.
          ?r : real.
            0 < r /\
            !P : real # real.
              sqdist (0, 0) P < r ==> P IN T
      in
      let converges_to =
        \(a : num -> real # real) (L : real # real).
          !e : real.
            0 < e
            ==>
            ?N : num.
              !n : num.
                N <= n ==> sqdist (a n) L < e
      in
      let closed_plane =
        \T : (real # real) set.
          !(a : num -> real # real) (L : real # real).
            (!n : num. a n IN T) /\ converges_to a L
            ==>
            L IN T
      in
      let has_outside_point_on_every_ray =
        \T : (real # real) set.
          !P : real # real.
            P <> (0, 0)
            ==>
            ?Q : real # real. ?k : real.
              0 < k /\
              Q = (k * FST P, k * SND P) /\
              Q NOTIN T
      in
      let bounded_plane =
        \T : (real # real) set.
          ?B : real.
            0 < B /\
            !P : real # real.
              P IN T ==> sqdist (0, 0) P <= B
      in
        convex_plane S /\
        (0, 0) IN S /\
        (origin_interior S \/ closed_plane S) /\
        has_outside_point_on_every_ray S
        ==>
        bounded_plane S``;
