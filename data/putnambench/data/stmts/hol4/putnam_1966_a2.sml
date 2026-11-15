(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a2:
  the side lengths, semiperimeter, and inradius of a nondegenerate real-plane
  triangle satisfy the stated reciprocal-square inequality. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1966_a2 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let collinear =
      \P Q R : real # real.
        (FST P - FST R) * (SND Q - SND R) =
        (SND P - SND R) * (FST Q - FST R)
    in
    let in_convex_hull =
      \Z A B C : real # real.
        ?u v w : real.
          0 <= u /\ 0 <= v /\ 0 <= w /\ u + v + w = 1 /\
          Z = (u * FST A + v * FST B + w * FST C,
               u * SND A + v * SND B + w * SND C)
    in
      !r a b c p : real. !A B C : real # real.
        a = dist B C /\
        b = dist C A /\
        c = dist A B /\
        p = (dist B C + dist C A + dist A B) / 2 /\
        ~collinear A B C /\
        (?I : real # real.
           (?!P : real # real.
              dist I P = r /\ collinear P B C) /\
           (?!Q : real # real.
              dist I Q = r /\ collinear Q C A) /\
           (?!R : real # real.
              dist I R = r /\ collinear R A B) /\
           (!Z : real # real.
              dist I Z <= r ==> in_convex_hull Z A B C))
        ==>
        1 / ((p - a) pow 2) +
        1 / ((p - b) pow 2) +
        1 / ((p - c) pow 2) >=
        1 / (r pow 2)``;
