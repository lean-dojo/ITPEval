(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a1:
  area bounds for a triangle formed by points on the sides of a nondegenerate
  real-plane triangle. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1973_a1 =
  ``let collinear =
      \P Q R : real # real.
        (FST P - FST R) * (SND Q - SND R) =
        (SND P - SND R) * (FST Q - FST R)
    in
    let in_closed_segment =
      \X U V : real # real.
        ?t : real.
          0 <= t /\ t <= 1 /\
          X = ((1 - t) * FST U + t * FST V,
               (1 - t) * SND U + t * SND V)
    in
    let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let triangle_area =
      \A B C : real # real.
        abs ((FST B - FST A) * (SND C - SND A) -
             (SND B - SND A) * (FST C - FST A)) / 2
    in
      !A B C X Y Z : real # real.
        ~collinear A B C /\
        in_closed_segment X B C /\
        in_closed_segment Y C A /\
        in_closed_segment Z A B
        ==>
        (((dist B X <= dist X C /\
           dist C Y <= dist Y A /\
           dist A Z <= dist Z B)
          ==>
          triangle_area X Y Z >=
            (1 / 4) * triangle_area A B C) /\
         (triangle_area A Z Y <= triangle_area X Y Z \/
          triangle_area B X Z <= triangle_area X Y Z \/
          triangle_area C Y X <= triangle_area X Y Z))``;
