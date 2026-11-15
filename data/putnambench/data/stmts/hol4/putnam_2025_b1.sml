(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b1:
  a Boolean coloring of the real Euclidean plane that preserves the color of
  every noncollinear triangle at its circumcenter is constant. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory;

val putnam_2025_b1 =
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
    let circumcenter =
      \A B C : real # real.
        @center : real # real.
          squared_distance center A = squared_distance center B /\
          squared_distance center B = squared_distance center C
    in
      !color : (real # real) -> bool.
        (!A B C : real # real.
           noncollinear A B C /\
           color A = color B /\
           color A = color C
           ==>
           color (circumcenter A B C) = color A)
        ==>
        ?c : bool.
          !P : real # real. color P = c``;
