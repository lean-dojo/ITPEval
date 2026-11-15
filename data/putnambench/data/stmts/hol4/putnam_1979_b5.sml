(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1979_b5:
  a closed convex plane set containing no nonzero lattice point and having
  equal area in the four quadrants has total area at most four. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory metricTheory topologyTheory realTheory;
open real_topologyTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_1979_b5 =
  ``!(C : (real # real) set).
      let convex_plane =
        \S : (real # real) set.
          !P Q : real # real. !u : real.
            P IN S /\ Q IN S /\ 0 <= u /\ u <= 1
            ==>
            ((1 - u) * FST P + u * FST Q,
             (1 - u) * SND P + u * SND Q) IN S
      in
      let area = measure (prod_measure_space lebesgue lebesgue)
      in
        closed_in (mtop mr2) C /\
        convex_plane C /\
        (0, 0) IN C /\
        (!a b : int.
           (a <> 0 \/ b <> 0)
           ==>
           (real_of_int a, real_of_int b) NOTIN C) /\
        area (C INTER
          {p : real # real | 0 <= FST p /\ 0 <= SND p}) =
          area (C INTER
            {p : real # real | 0 <= FST p /\ SND p <= 0}) /\
        area (C INTER
          {p : real # real | 0 <= FST p /\ SND p <= 0}) =
          area (C INTER
            {p : real # real | FST p <= 0 /\ 0 <= SND p}) /\
        area (C INTER
          {p : real # real | FST p <= 0 /\ 0 <= SND p}) =
          area (C INTER
            {p : real # real | FST p <= 0 /\ SND p <= 0})
        ==>
        area C <= Normal 4``;
