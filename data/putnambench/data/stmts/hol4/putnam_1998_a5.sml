(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a5:
  a finite cover of a plane set by positive-radius open discs has a pairwise
  disjoint subcollection whose triple-radius discs still cover the set. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val putnam_1998_a5 =
  ``let open_disc =
      \(centre : real # real) (radius : real).
        {P : real # real |
           (FST P - FST centre) pow 2 +
           (SND P - SND centre) pow 2 < radius pow 2}
    in
      !k : num.
      !c : num -> real # real.
      !r : num -> real.
      !E : (real # real) set.
        (!i : num. i IN count k ==> 0 < r i) /\
        E SUBSET
          BIGUNION (IMAGE (\i. open_disc (c i) (r i)) (count k))
        ==>
        ?n : num. ?t : num -> num.
          n <= k /\
          IMAGE t (count n) SUBSET count k /\
          (!i j : num.
             i IN count n /\ j IN count n /\ i <> j
             ==>
             DISJOINT
               (open_disc (c (t i)) (r (t i)))
               (open_disc (c (t j)) (r (t j)))) /\
          E SUBSET
            BIGUNION
              (IMAGE
                 (\i. open_disc (c (t i)) (3 * (r (t i))))
                 (count n))``;
