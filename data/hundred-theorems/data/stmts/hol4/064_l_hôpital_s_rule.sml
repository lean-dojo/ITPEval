(*
  Statement-only formalization of "L'Hôpital's Rule" from Hundred Theorems
  artifact 064. For real functions tending to zero at a point, differentiable
  throughout a punctured neighborhood there with nonzero denominator
  derivative, convergence of the quotient of derivatives implies convergence
  of the quotient of the functions to the same finite limit. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val lhopitals_rule =
  ``!f g f' g' c L d.
      0 < d /\
      (!x.
         0 < abs (x - c) /\ abs (x - c) < d
         ==>
         (f diffl (f' x)) x /\
         (g diffl (g' x)) x /\
         g' x <> 0) /\
      (f -> 0) c /\
      (g -> 0) c /\
      ((\x. f' x / g' x) -> L) c
      ==>
      ((\x. f x / g x) -> L) c``;
