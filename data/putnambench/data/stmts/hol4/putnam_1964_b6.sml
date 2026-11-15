(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b6:
  impossibility of partitioning the closed unit disk in the real Euclidean
  plane into two disjoint congruent sets. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;

val putnam_1964_b6 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let D =
      {P : real # real | dist (0, 0) P <= 1}
    in
    let cong =
      \A B : (real # real) set.
        ?f : real # real -> real # real.
          B = IMAGE f A /\
          !P Q : real # real. dist P Q = dist (f P) (f Q)
    in
      ~(?A B : (real # real) set.
          cong A B /\
          A INTER B = EMPTY /\
          A UNION B = D)``;
