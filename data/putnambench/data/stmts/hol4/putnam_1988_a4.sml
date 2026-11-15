(*
  Statement-only formalization of PutnamBench artifact putnam_1988_a4:
  every three-coloring of the real Euclidean plane has a monochromatic
  unit-distance pair, while the analogous claim for nine colors is false.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory realTheory transcTheory;

val putnam_1988_a4 =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let p =
      \n : num.
        !color : real # real -> num.
          (!v : real # real. color v < n)
          ==>
          ?P Q : real # real.
            color P = color Q /\ dist P Q = 1
    in
      (p 3 <=> T) /\ (p 9 <=> F)``;
