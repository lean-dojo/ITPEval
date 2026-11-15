(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b1:
  five points on the real unit circle maximize the sum of their ten pairwise
  distances exactly when they can be cyclically ordered with one common
  positive side length. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory;
open transcTheory;

val putnam_1974_b1 =
  ``let sqdist =
      \P Q : real # real.
        (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2
    in
    let dist =
      \P Q : real # real. sqrt (sqdist P Q)
    in
    let norm =
      \P : real # real. sqrt (FST P pow 2 + SND P pow 2)
    in
    let on_unit_circle =
      \p : num -> real # real.
        !i : num. i < 5 ==> norm (p i) = 1
    in
    let distance_sum =
      \p : num -> real # real.
        SIGMA
          (\j : num.
             SIGMA
               (\i : num.
                  if i < j then dist (p i) (p j) else 0)
               (count 5))
          (count 5)
    in
    let permutes_five =
      \ord : num -> num.
        (!i : num. i < 5 ==> ord i < 5) /\
        (!i j : num.
           i < 5 /\ j < 5 /\ ord i = ord j ==> i = j) /\
        (!j : num. j < 5 ==> ?i : num. i < 5 /\ ord i = j)
    in
    let regular_configuration =
      \p : num -> real # real.
        (!i j : num.
           i < 5 /\ j < 5 /\ i <> j ==> p i <> p j) /\
        ?B : real. ?ord : num -> num.
          0 < B /\
          permutes_five ord /\
          !i : num.
            i < 5
            ==>
            dist (p (ord i)) (p (ord ((i + 1) MOD 5))) = B
    in
      !p : num -> real # real.
        on_unit_circle p
        ==>
        ((!q : num -> real # real.
            on_unit_circle q ==> distance_sum q <= distance_sum p) <=>
         regular_configuration p)``;
