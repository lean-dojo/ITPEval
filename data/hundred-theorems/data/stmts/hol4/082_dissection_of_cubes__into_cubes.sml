(*
  Statement-only formalization of Hundred Theorems artifact 082, "Dissection
  of Cubes (into Cubes)": in every finite real dimension at least three, the
  unit cube has no finite dissection into at least two pairwise disjoint
  axis-aligned cubes with positive, pairwise distinct side lengths. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val dissection_of_cubes_into_cubes =
  ``!(s : (('i -> real) # real) set).
      let cube_set =
        \(c : ('i -> real) # real).
          {x : 'i -> real |
             !j. FST c j <= x j /\ x j < FST c j + SND c}
      in
      let unit_cube =
        {x : 'i -> real | !j. 0 <= x j /\ x j < 1}
      in
        FINITE (UNIV : 'i set) /\
        3 <= CARD (UNIV : 'i set) /\
        FINITE s /\
        (!c. c IN s ==> 0 < SND c) /\
        (?c d. c IN s /\ d IN s /\ c <> d) /\
        (!c d.
           c IN s /\ d IN s /\ c <> d ==>
           DISJOINT (cube_set c) (cube_set d)) /\
        (!x.
           x IN unit_cube <=>
           ?c. c IN s /\ x IN cube_set c) /\
        (!c d.
           c IN s /\ d IN s /\ SND c = SND d ==>
           c = d)
        ==>
        F``;
