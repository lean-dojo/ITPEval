(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b6:
  a nondegenerate quadrilateral tangent to an interior circle and having
  area equal to the square root of the product of its side lengths is cyclic.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory;

val putnam_1970_b6 =
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
    let collinear_set =
      \T : (real # real) set.
        !P Q R : real # real.
          P IN T /\ Q IN T /\ R IN T ==> collinear P Q R
    in
    let closed_segment =
      \A B : real # real.
      \X : real # real.
        ?t : real.
          0 <= t /\ t <= 1 /\
          X = ((1 - t) * FST A + t * FST B,
               (1 - t) * SND A + t * SND B)
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
    let in_interior4 =
      \A B C D X : real # real.
        ?e : real.
          0 < e /\
          !Y : real # real.
            sqdist X Y < e pow 2 ==> in_convex_hull4 A B C D Y
    in
      !L : num -> real # real.
        let S = {L 0; L 1; L 2; L 3}
        in
          CARD S = 4 /\
          (!T : (real # real) set.
             T SUBSET S /\ CARD T = 3 ==> ~collinear_set T) /\
          dist (L 0) (L 1) > 0 /\
          dist (L 1) (L 2) > 0 /\
          dist (L 2) (L 3) > 0 /\
          dist (L 3) (L 0) > 0 /\
          (!i : num.
             i < 4
             ==>
             !X : real # real.
               closed_segment (L i) (L ((i + 1) MOD 4)) X
               ==>
               ~in_interior4 (L 0) (L 1) (L 2) (L 3) X) /\
          (?O : real # real. ?r : real.
             in_convex_hull4 (L 0) (L 1) (L 2) (L 3) O /\
             r > 0 /\
             !i : num.
               i < 4
               ==>
               ?!I : real # real.
                 collinear I (L i) (L ((i + 1) MOD 4)) /\
                 dist O I = r) /\
          measure (prod_measure_space lebesgue lebesgue)
            {X | in_convex_hull4 (L 0) (L 1) (L 2) (L 3) X} =
            Normal
              (sqrt
                (dist (L 0) (L 1) * dist (L 1) (L 2) *
                 dist (L 2) (L 3) * dist (L 3) (L 0)))
          ==>
          ?O : real # real. ?r : real.
            !P : real # real. P IN S ==> dist P O = r``;
