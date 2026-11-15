(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a6:
  vanishing integrals over all centered maximal axis-parallel squares in the
  unit square force a continuous real function to vanish there. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory metricTheory topologyTheory realTheory;
open real_topologyTheory integrationTheory;

val putnam_1977_a6 =
  ``let X =
      \P : real # real.
        0 <= FST P /\ FST P <= 1 /\
        0 <= SND P /\ SND P <= 1
    in
    let room =
      \P : real # real.
        min (min (FST P) (1 - FST P))
            (min (SND P) (1 - SND P))
    in
    let solution = T
    in
      ((!f : real # real -> real.
          continuous_map (mtop mr2, euclidean) f
          ==>
          ((!P : real # real.
              X P
              ==>
              integration$integral
                (interval [FST P - room P, FST P + room P])
                (\x : real.
                   integration$integral
                     (interval [SND P - room P, SND P + room P])
                     (\y : real. f (x, y))) =
              0)
           ==>
           !P : real # real. X P ==> f P = 0))
       <=>
       solution)``;
