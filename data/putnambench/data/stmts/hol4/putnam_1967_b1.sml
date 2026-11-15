(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b1:
  the midpoints of the three unconstrained sides of a cyclic hexagon whose
  alternating side lengths equal the radius form an equilateral triangle.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory
     transcTheory;

val putnam_1967_b1 =
  ``let sqdist =
      \P Q : real # real.
        (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2
    in
    let dist =
      \P Q : real # real. sqrt (sqdist P Q)
    in
    let midpoint =
      \P Q : real # real.
        ((FST P + FST Q) / 2, (SND P + SND Q) / 2)
    in
    let closed_segment =
      \A B : real # real.
      \X : real # real.
        ?t : real.
          0 <= t /\ t <= 1 /\
          X = ((1 - t) * FST A + t * FST B,
               (1 - t) * SND A + t * SND B)
    in
    let in_convex_hull =
      \L : num -> real # real.
      \X : real # real.
        ?w : num -> real.
          (!i : num. i < 6 ==> 0 <= w i) /\
          SIGMA w (count 6) = 1 /\
          X = (SIGMA (\i : num. w i * FST (L i)) (count 6),
               SIGMA (\i : num. w i * SND (L i)) (count 6))
    in
    let in_interior =
      \L : num -> real # real.
      \X : real # real.
        ?e : real.
          0 < e /\
          !Y : real # real.
            sqdist X Y < e pow 2 ==> in_convex_hull L Y
    in
      !r : real. !L : num -> real # real. !P Q R : real # real.
        P = midpoint (L 1) (L 2) /\
        Q = midpoint (L 3) (L 4) /\
        R = midpoint (L 5) (L 0) /\
        0 < r /\
        (?O : real # real.
           !i : num.
             i < 6 ==> dist O (L i) = r) /\
        (!i j : num.
           i < 6 /\ j < 6 /\ i <> j
           ==>
           (i + 1) MOD 6 = j \/
           i = (j + 1) MOD 6 \/
           ?X : real # real.
             closed_segment (L i) (L j) X /\
             in_interior L X) /\
        dist (L 0) (L 1) = r /\
        dist (L 2) (L 3) = r /\
        dist (L 4) (L 5) = r /\
        L 1 <> L 2 /\ L 3 <> L 4 /\ L 5 <> L 0
        ==>
        dist P Q = dist R P /\ dist Q R = dist P Q``;
