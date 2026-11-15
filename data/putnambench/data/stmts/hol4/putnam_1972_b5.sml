(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b5:
  a skew quadrilateral in real three-space with two pairs of equal opposite
  vertex angles has equal corresponding opposite side lengths. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1972_b5 =
  ``let zero3 = ((0, 0), 0) : (real # real) # real
    in
    let add3 =
      \P Q : (real # real) # real.
        ((FST (FST P) + FST (FST Q),
          SND (FST P) + SND (FST Q)),
         SND P + SND Q)
    in
    let sub3 =
      \P Q : (real # real) # real.
        ((FST (FST P) - FST (FST Q),
          SND (FST P) - SND (FST Q)),
         SND P - SND Q)
    in
    let smul3 =
      \c : real.
      \P : (real # real) # real.
        ((c * FST (FST P), c * SND (FST P)), c * SND P)
    in
    let dot3 =
      \P Q : (real # real) # real.
        FST (FST P) * FST (FST Q) +
        SND (FST P) * SND (FST Q) +
        SND P * SND Q
    in
    let norm3 =
      \P : (real # real) # real. sqrt (dot3 P P)
    in
    let dist3 =
      \P Q : (real # real) # real. norm3 (sub3 P Q)
    in
    let vangle3 =
      \u v : (real # real) # real.
        if u = zero3 \/ v = zero3 then
          pi / 2
        else
          acs (dot3 u v / (norm3 u * norm3 v))
    in
    let angle3 =
      \P Q R : (real # real) # real.
        vangle3 (sub3 P Q) (sub3 R Q)
    in
    let among4 =
      \A B C D x : (real # real) # real.
        x = A \/ x = B \/ x = C \/ x = D
    in
    let coplanar4 =
      \A B C D : (real # real) # real.
        ?u v : (real # real) # real.
          !x y : (real # real) # real.
            among4 A B C D x /\ among4 A B C D y
            ==>
            ?c d : real.
              sub3 x y = add3 (smul3 c u) (smul3 d v)
    in
      !A B C D : (real # real) # real.
        ~coplanar4 A B C D /\
        angle3 A B C = angle3 C D A /\
        angle3 B C D = angle3 D A B
        ==>
        dist3 A B = dist3 C D /\
        dist3 B C = dist3 D A``;
