(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a1:
  among six distinct points in the real Euclidean plane, the ratio of the
  longest pairwise distance to the shortest is at least sqrt 3. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;

val putnam_1964_a1 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
      !(A : (real # real) set).
        FINITE A /\
        CARD A = 6
        ==>
        let dists =
          {r : real |
             ?P Q : real # real.
               P IN A /\ Q IN A /\ P <> Q /\ r = dist P Q}
        in
          ?D d : real.
            D IN dists /\
            d IN dists /\
            (!r : real. r IN dists ==> r <= D) /\
            (!r : real. r IN dists ==> d <= r) /\
            D / d >= sqrt 3``;
