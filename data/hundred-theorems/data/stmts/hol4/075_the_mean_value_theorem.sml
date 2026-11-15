(*
  Statement-only formalization of "The Mean Value Theorem" from Hundred
  Theorems artifact 075. A real function continuous on a closed interval and
  differentiable on its interior has an interior point where its derivative
  realizes the secant slope. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val mean_value_theorem =
  ``!f a b.
      a < b /\
      (!x. a <= x /\ x <= b ==> f contl x) /\
      (!x. a < x /\ x < b ==> f differentiable x)
      ==>
      ?l z.
        a < z /\ z < b /\
        (f diffl l) z /\
        f b - f a = (b - a) * l``;
