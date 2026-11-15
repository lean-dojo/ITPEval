(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b1:
  a convex polygon contained in the unit square has sum of squared side
  lengths at most 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory;

val putnam_1966_b1 =
  ``let sqdist =
      \P Q : real # real.
        (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2
    in
    let dist =
      \P Q : real # real. sqrt (sqdist P Q)
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
    let in_convex_hull =
      \n : num.
      \L : num -> real # real.
      \X : real # real.
        ?w : num -> real.
          (!i : num. i < n ==> 0 <= w i) /\
          SIGMA w (count n) = 1 /\
          X = (SIGMA (\i : num. w i * FST (L i)) (count n),
               SIGMA (\i : num. w i * SND (L i)) (count n))
    in
    let in_interior =
      \n : num.
      \L : num -> real # real.
      \X : real # real.
        ?r : real.
          0 < r /\
          !Y : real # real.
            sqdist X Y < r pow 2 ==> in_convex_hull n L Y
    in
      !n : num. !L : num -> real # real.
        3 <= n /\
        (!i : num.
           i < n
           ==>
           0 <= FST (L i) /\ FST (L i) <= 1 /\
           0 <= SND (L i) /\ SND (L i) <= 1) /\
        (!i j k : num.
           i < n /\ j < n /\ k < n /\
           i <> j /\ j <> k /\ k <> i
           ==>
           ~collinear (L i) (L j) (L k)) /\
        (!i : num.
           i < n
           ==>
           !X : real # real.
             closed_segment (L i) (L ((i + 1) MOD n)) X
             ==>
             ~in_interior n L X)
        ==>
        SIGMA
          (\i : num. dist (L i) (L ((i + 1) MOD n)) pow 2)
          (count n)
        <= 4``;
