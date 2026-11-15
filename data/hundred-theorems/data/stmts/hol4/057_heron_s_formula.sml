(*
  Statement-only formalization of Hundred Theorems artifact 057_heron_s_formula,
  cataloged as "Heron's Formula": the area of a triangle in the real Euclidean
  plane is determined by its side lengths and semiperimeter. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val herons_formula =
  ``let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let triangle_area =
      \A B C : real # real.
        abs ((FST B - FST A) * (SND C - SND A) -
             (SND B - SND A) * (FST C - FST A)) / 2
    in
      !A B C : real # real.
        let a = dist C B in
        let b = dist A C in
        let c = dist B A in
        let s = (a + b + c) / 2 in
          triangle_area A B C =
          sqrt (s * (s - a) * (s - b) * (s - c))``;
