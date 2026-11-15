(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a2:
  the midpoint locus determined by circles of radii 1 and 3 whose centers are
  10 units apart is a closed annulus about the centers' midpoint. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory;

val putnam_1996_a2 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let midpoint =
      \P Q : real # real.
        ((FST P + FST Q) / 2, (SND P + SND Q) / 2)
    in
      !(O1 O2 : real # real). !(C1 C2 : (real # real) set).
        C1 = {P : real # real | dist P O1 = 1} /\
        C2 = {P : real # real | dist P O2 = 3} /\
        dist O1 O2 = 10
        ==>
        {M : real # real |
           ?X Y : real # real.
             X IN C1 /\ Y IN C2 /\ M = midpoint X Y} =
        {P : real # real |
           1 <= dist P (midpoint O1 O2) /\
           dist P (midpoint O1 O2) <= 2}``;
