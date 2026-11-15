(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b4:
  every continuous plane curve of Euclidean variation one on the unit
  interval is covered by a closed rectangle of area one quarter.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory
     real_topologyTheory transcTheory;

val putnam_1969_b4 =
  ``let sqdist =
      \P Q : real # real.
        (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2
    in
    let dist =
      \P Q : real # real. sqrt (sqdist P Q)
    in
    let monotone_partition =
      \u : num -> real.
        (!i j : num. i <= j ==> u i <= u j) /\
        (!i : num. 0 <= u i /\ u i <= 1)
    in
    let polygonal_sum =
      \G : real -> real # real.
      \n : num.
      \u : num -> real.
        SIGMA
          (\i : num. dist (G (u (i + 1))) (G (u i)))
          (count n)
    in
    let curve_length_one =
      \G : real -> real # real.
        (!n : num. !u : num -> real.
           monotone_partition u ==> polygonal_sum G n u <= 1) /\
        (!b : real.
           (!n : num. !u : num -> real.
              monotone_partition u ==> polygonal_sum G n u <= b)
           ==>
           1 <= b)
    in
    let in_convex_hull4 =
      \A B C D X : real # real.
        ?wa wb wc wd : real.
          0 <= wa /\ 0 <= wb /\ 0 <= wc /\ 0 <= wd /\
          wa + wb + wc + wd = 1 /\
          X =
            (wa * FST A + wb * FST B + wc * FST C + wd * FST D,
             wa * SND A + wb * SND B + wc * SND C + wd * SND D)
    in
    let right_angle =
      \P Q R : real # real.
        (FST P - FST Q) * (FST R - FST Q) +
        (SND P - SND Q) * (SND R - SND Q) = 0 /\
        0 <
          (FST P - FST Q) * (SND R - SND Q) -
          (SND P - SND Q) * (FST R - FST Q)
    in
      !G : real -> real # real.
        (\t : real. FST (G t)) continuous_on interval [0, 1] /\
        (\t : real. SND (G t)) continuous_on interval [0, 1] /\
        curve_length_one G
        ==>
        ?A B C D : real # real.
          (!t : real.
             0 <= t /\ t <= 1 ==> in_convex_hull4 A B C D (G t)) /\
          dist A B * dist B C = 1 / 4 /\
          right_angle A B C /\
          right_angle B C D /\
          right_angle C D A /\
          right_angle D A B``;
