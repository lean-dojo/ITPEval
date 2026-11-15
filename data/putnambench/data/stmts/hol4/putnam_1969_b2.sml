(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b2:
  no finite group is the union of two proper subgroups, while some finite
  group is the union of three proper subgroups. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory groupTheory;

val putnam_1969_b2 =
  ``let P =
      \n : num.
        !(g : num group) (H : num -> num group).
          FiniteGroup g /\
          (!i. i < n ==>
               Subgroup (H i) g /\ (H i).carrier <> g.carrier)
          ==>
          BIGUNION (IMAGE (\i. (H i).carrier) (count n)) <> g.carrier
    in
      P 2 /\ ~P 3``;
