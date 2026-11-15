(*
  Statement-only formalization of PutnamBench artifact putnam_1993_b5:
  no four points in the real Euclidean plane have all six pairwise distances
  equal to odd integers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory realTheory intrealTheory
     transcTheory;

val putnam_1993_b5 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let odd_integer_distance =
      \P Q : real # real.
        ?k : int.
          dist P Q = real_of_int k /\ ODD (Num (ABS k))
    in
      ~(?A B C D : real # real.
          odd_integer_distance A B /\
          odd_integer_distance A C /\
          odd_integer_distance A D /\
          odd_integer_distance B C /\
          odd_integer_distance B D /\
          odd_integer_distance C D)``;
