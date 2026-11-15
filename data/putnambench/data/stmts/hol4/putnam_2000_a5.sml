(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a5:
  three distinct integer-coordinate points on a circle of positive radius
  contain two points at least the cube root of the radius apart. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory realTheory intrealTheory
     transcTheory;

val putnam_2000_a5 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
      !r : real. !z : real # real. !S : (real # real) set.
        0 < r /\
        FINITE S /\
        CARD S = 3 /\
        (!P : real # real.
           P IN S
           ==>
           ?m n : int.
             FST P = real_of_int m /\
             SND P = real_of_int n) /\
        (!P : real # real. P IN S ==> dist P z = r)
        ==>
        ?P Q : real # real.
          P IN S /\
          Q IN S /\
          P <> Q /\
          r powr (1 / 3) <= dist P Q``;
