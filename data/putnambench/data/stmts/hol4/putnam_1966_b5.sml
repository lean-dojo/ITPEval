(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b5:
  any finite set of at least three real-plane points, with no three collinear,
  is the vertex set of a simple closed polygon. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val putnam_1966_b5 =
  ``let are_collinear =
      \P Q R : real # real.
        (FST P - FST R) * (SND Q - SND R) =
        (SND P - SND R) * (FST Q - FST R)
    in
    let on_closed_segment =
      \A B : real # real.
      \X : real # real.
        ?t : real.
          0 <= t /\ t <= 1 /\
          X = ((1 - t) * FST A + t * FST B,
               (1 - t) * SND A + t * SND B)
    in
      !(S : (real # real) set).
        FINITE S /\
        3 <= CARD S /\
        (!P Q R : real # real.
           P IN S /\ Q IN S /\ R IN S /\
           P <> Q /\ P <> R /\ Q <> R
           ==>
           ~are_collinear P Q R)
        ==>
        ?L : num -> real # real.
          (!p : real # real.
             p IN S
             ==>
             ?!i : num. i < CARD S /\ p = L i) /\
          (!i j : num.
             i < CARD S /\ j < CARD S /\ i <> j
             ==>
             !I : real # real.
               on_closed_segment (L i) (L ((i + 1) MOD CARD S)) I /\
               on_closed_segment (L j) (L ((j + 1) MOD CARD S)) I
               ==>
               I = L i \/
               I = L ((i + 1) MOD CARD S) \/
               I = L j \/
               I = L ((j + 1) MOD CARD S))``;
