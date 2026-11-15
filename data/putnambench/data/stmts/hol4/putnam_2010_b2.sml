(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b2:
  the least possible distance between two vertices of a noncollinear lattice
  triangle whose three side lengths are integers is 3. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory intrealTheory transcTheory;

val putnam_2010_b2 =
  ``let dist =
      \P Q : int # int.
        sqrt
          ((real_of_int (FST P - FST Q)) pow 2 +
           (real_of_int (SND P - SND Q)) pow 2)
    in
    let noncollinear =
      \A B C : int # int.
        (FST B - FST A) * (SND C - SND A) <>
        (SND B - SND A) * (FST C - FST A)
    in
    let integral_distance =
      \P Q : int # int.
        ?n : num. dist P Q = (&n : real)
    in
    let admissible =
      \A B C : int # int.
        noncollinear A B C /\
        integral_distance A B /\
        integral_distance A C /\
        integral_distance B C
    in
      (!A B C : int # int.
         admissible A B C ==> (3 : real) <= dist A B) /\
      (?A B C : int # int.
         admissible A B C /\ dist A B = (3 : real))``;
