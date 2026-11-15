(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a6:
  four plane points with no three collinear and with all six squared pairwise
  distances rational have a rational ratio of the areas of triangles ABC and
  ABD. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory ratTheory real_of_ratTheory;

val putnam_2018_a6 =
  ``let cross =
      \A B C : real # real.
        (FST B - FST A) * (SND C - SND A) -
        (SND B - SND A) * (FST C - FST A)
    in
    let noncollinear =
      \A B C : real # real. cross A B C <> 0
    in
    let squared_distance =
      \P Q : real # real.
        (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2
    in
    let rational_squared_distance =
      \P Q : real # real.
        P <> Q /\
        ?q : rat. squared_distance P Q = real_of_rat q
    in
    let triangle_area =
      \A B C : real # real. abs (cross A B C) / 2
    in
      !A B C D : real # real.
        noncollinear A B C /\
        noncollinear A B D /\
        noncollinear A C D /\
        noncollinear B C D /\
        rational_squared_distance A B /\
        rational_squared_distance A C /\
        rational_squared_distance A D /\
        rational_squared_distance B C /\
        rational_squared_distance B D /\
        rational_squared_distance C D
        ==>
        ?q : rat.
          triangle_area A B C / triangle_area A B D =
          real_of_rat q``;
