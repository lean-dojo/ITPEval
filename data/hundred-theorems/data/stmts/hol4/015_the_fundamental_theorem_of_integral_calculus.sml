(*
  Statement-only formalization of "The Fundamental Theorem of Integral Calculus" from Hundred
  Theorems item 015. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integralTheory;

val fundamental_theorem_of_integral_calculus =
  ``!f f' a b.
      a <= b /\
      (!x. a <= x /\ x <= b ==> (f diffl (f' x)) x)
      ==>
      Dint (a,b) f' (f b - f a)``;
