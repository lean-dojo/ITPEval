(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a2:
  the least possible Lebesgue area of a convex plane set meeting both branches
  of xy = 1 and both branches of xy = -1 is four. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_2007_a2 =
  ``let convex_plane =
      \S : (real # real) set.
        !P Q : real # real. !u : real.
          P IN S /\ Q IN S /\ 0 <= u /\ u <= 1
          ==>
          ((1 - u) * FST P + u * FST Q,
           (1 - u) * SND P + u * SND Q) IN S
    in
    let meets_all_branches =
      \S : (real # real) set.
        (?P : real # real.
           P IN S /\ 0 < FST P /\ 0 < SND P /\ FST P * SND P = 1) /\
        (?P : real # real.
           P IN S /\ FST P < 0 /\ SND P < 0 /\ FST P * SND P = 1) /\
        (?P : real # real.
           P IN S /\ FST P < 0 /\ 0 < SND P /\ FST P * SND P = -1) /\
        (?P : real # real.
           P IN S /\ 0 < FST P /\ SND P < 0 /\ FST P * SND P = -1)
    in
    let admissible =
      \S : (real # real) set.
        convex_plane S /\ meets_all_branches S
    in
    let area =
      measure (prod_measure_space lebesgue lebesgue)
    in
      (?S : (real # real) set.
         admissible S /\ area S = Normal 4) /\
      (!S : (real # real) set.
         admissible S ==> Normal 4 <= area S)``;
