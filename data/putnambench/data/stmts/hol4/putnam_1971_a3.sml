(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a3:
  three distinct lattice points on a circle of positive radius have side-length
  product at least twice the radius. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory intrealTheory transcTheory;

val putnam_1971_a3 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let lattice_point =
      \P : real # real.
        ?m n : int.
          FST P = real_of_int m /\ SND P = real_of_int n
    in
      !a b c : real # real. !R : real.
        lattice_point a /\
        lattice_point b /\
        lattice_point c /\
        a <> b /\ a <> c /\ b <> c /\
        0 < R /\
        (?C : real # real.
           dist a C = R /\ dist b C = R /\ dist c C = R)
        ==>
        dist a b * dist a c * dist b c >= 2 * R``;
