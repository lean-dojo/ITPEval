(*
  Statement-only formalization of "The Impossibility of Trisecting the Angle and Doubling the
  Cube" from Hundred Theorems item 008. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory realTheory transcTheory;

val impossibility_of_trisecting_the_angle_and_doubling_the_cube =
  ``!(h8_rat : real -> bool)
      (h8_dist : real # real -> real # real -> real)
      (h8_parallel :
         real # real -> real # real ->
         real # real -> real # real -> bool)
      (h8_collinear :
         real # real -> real # real -> real # real -> bool)
      (h8_intersection :
         real # real -> real # real -> real # real ->
         real # real -> real # real -> bool)
      (h8_constructible : real # real -> bool).
      ((!x : real.
          h8_rat x <=>
          ?m n : num.
            ~(n = 0) /\
            (x = (&m : real) / (&n : real) \/
             x = ~((&m : real) / (&n : real)))) /\
       (!P Q : real # real.
          h8_dist P Q =
            sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)) /\
       (!A B C D : real # real.
          h8_parallel A B C D <=>
            (FST A - FST B) * (SND C - SND D) =
            (SND A - SND B) * (FST C - FST D)) /\
       (!A M B : real # real.
          h8_collinear A M B <=> h8_parallel A M A B) /\
       (!M A B C D : real # real.
          h8_intersection M A B C D <=>
            h8_collinear A M B /\ h8_collinear C M D) /\
       (!M : real # real.
          h8_constructible M <=>
          !(S : real # real -> bool).
            ((!P : real # real.
                h8_rat (FST P) /\ h8_rat (SND P) ==> S P) /\
             (!A B C D P : real # real.
                S A /\ S B /\ S C /\ S D /\
                ~h8_parallel A B C D /\
                h8_intersection P A B C D
                ==> S P) /\
             (!A B C D E P : real # real.
                S A /\ S B /\ S C /\ S D /\ S E /\
                ~(A = B) /\
                h8_collinear A P B /\
                h8_dist C P = h8_dist D E
                ==> S P) /\
             (!A B C D E F P : real # real.
                S A /\ S B /\ S C /\ S D /\ S E /\ S F /\
                ~(A = D /\ h8_dist B C = h8_dist E F) /\
                h8_dist A P = h8_dist B C /\
                h8_dist D P = h8_dist E F
                ==> S P))
            ==> S M))
      ==>
      ((!x : real.
          x pow 3 = 2 ==> ~h8_constructible (x, 0)) /\
       (!y : real.
          ~h8_constructible (cos (pi / 9), y)))``;
