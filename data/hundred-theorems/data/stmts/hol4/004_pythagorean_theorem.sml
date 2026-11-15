(*
  Statement-only formalization of "Pythagorean Theorem" from Hundred Theorems item 004:
  orthogonal sides at a vertex in the real Euclidean plane satisfy the squared-distance
  identity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory;

val pythagorean_theorem =
  ``!A B C : real # real.
      (FST A - FST B) * (FST C - FST B) +
          (SND A - SND B) * (SND C - SND B) = 0
      ==>
      (FST C - FST A) pow 2 + (SND C - SND A) pow 2 =
        ((FST B - FST A) pow 2 + (SND B - SND A) pow 2) +
        ((FST C - FST B) pow 2 + (SND C - SND B) pow 2)``;
