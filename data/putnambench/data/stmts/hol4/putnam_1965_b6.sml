(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b6:
  four distinct points in the real Euclidean plane whose two designated
  pencils of circles always intersect are collinear or cocyclic. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1965_b6 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let on_circle =
      \radius : real.
      \centre point : real # real.
        dist centre point = radius
    in
    let collinear =
      \P Q R : real # real.
        (FST P - FST Q) * (SND R - SND Q) =
        (SND P - SND Q) * (FST R - FST Q)
    in
    let pairwise_distinct =
      \A B C D : real # real.
        A <> B /\ A <> C /\ A <> D /\
        B <> C /\ B <> D /\ C <> D
    in
      !A B C D : real # real.
        pairwise_distinct A B C D /\
        (!r s : real. !P Q : real # real.
           0 < r /\ 0 < s /\
           on_circle r P A /\ on_circle r P B /\
           on_circle s Q C /\ on_circle s Q D
           ==>
           ?I : real # real.
             on_circle r P I /\ on_circle s Q I)
        ==>
        (collinear A B C /\ collinear A B D) \/
        ?r : real. ?P : real # real.
          0 < r /\
          on_circle r P A /\ on_circle r P B /\
          on_circle r P C /\ on_circle r P D``;
