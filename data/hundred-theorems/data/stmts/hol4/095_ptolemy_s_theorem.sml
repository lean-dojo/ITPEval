(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__095, cataloged as "Ptolemy's Theorem": four
  cyclically ordered points on a circle in the real Euclidean plane satisfy
  Ptolemy's distance identity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val ptolemys_theorem =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let circle_point =
      \P centre radius angle : real # real.
        FST P = FST centre + radius * cos angle /\
        SND P = SND centre + radius * sin angle
    in
      !A B C D centre : real # real.
      !radius a b c d : real.
        circle_point A centre radius a /\
        circle_point B centre radius b /\
        circle_point C centre radius c /\
        circle_point D centre radius d /\
        0 <= radius /\
        0 <= a /\ a <= b /\ b <= c /\ c <= d /\ d <= 2 * pi
        ==>
        dist A C * dist B D =
          dist A B * dist C D + dist A D * dist B C``;
