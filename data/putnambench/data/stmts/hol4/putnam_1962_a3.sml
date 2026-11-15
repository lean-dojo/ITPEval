(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a3:
  the area ratio of the triangle formed by three cevian intersections in a
  nondegenerate real-plane triangle. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1962_a3 =
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
      !A B C Ap Bp Cp P Q R : real # real. !k : real.
        0 < k /\
        ~collinear A B C /\
        in_closed_segment Ap B C /\
        dist C Ap / dist Ap B = k /\
        in_closed_segment Bp C A /\
        dist A Bp / dist Bp C = k /\
        in_closed_segment Cp A B /\
        dist B Cp / dist Cp A = k /\
        in_closed_segment P B Bp /\
        in_closed_segment P C Cp /\
        in_closed_segment Q C Cp /\
        in_closed_segment Q A Ap /\
        in_closed_segment R A Ap /\
        in_closed_segment R B Bp
        ==>
        triangle_area P Q R / triangle_area A B C =
          (k - 1) pow 2 / (k pow 2 + k + 1)``;
