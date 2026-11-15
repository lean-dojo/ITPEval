(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a4:
  equal finite red and blue sets of real-plane points in general position
  admit a perfect red-blue matching by pairwise disjoint closed segments.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory;

val putnam_1979_a4 =
  ``let collinear =
      \P Q N : real # real.
        (FST Q - FST P) * (SND N - SND P) =
        (SND Q - SND P) * (FST N - FST P)
    in
    let segment_point =
      \L : (real # real) # (real # real).
      \t : real.
        (t * FST (FST L) + (1 - t) * FST (SND L),
         t * SND (FST L) + (1 - t) * SND (SND L))
    in
      !R B : (real # real) set.
        FINITE R /\
        FINITE B /\
        CARD R = CARD B /\
        DISJOINT R B /\
        (!P Q N : real # real.
           P IN R UNION B /\
           Q IN R UNION B /\
           N IN R UNION B /\
           P <> Q /\ P <> N /\ Q <> N
           ==>
           ~collinear P Q N)
        ==>
        ?V : ((real # real) # (real # real)) set.
          FINITE V /\
          CARD V = CARD R /\
          (!L : (real # real) # (real # real).
             L IN V
             ==>
             FST L IN R /\ SND L IN B) /\
          (!L M : (real # real) # (real # real).
             L IN V /\ M IN V /\ L <> M
             ==>
             FST L <> FST M /\
             SND L <> SND M /\
             !x y : real.
               0 <= x /\ x <= 1 /\ 0 <= y /\ y <= 1
               ==>
               segment_point L x <> segment_point M y)``;
