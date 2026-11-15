(*
  Statement-only formalization of "The Intermediate Value Theorem" from
  Hundred Theorems artifact 079. A real function continuous on a closed
  interval attains every value between its endpoint values. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val intermediate_value_theorem =
  ``!f a b y.
      a <= b /\
      f a <= y /\ y <= f b /\
      (!x. a <= x /\ x <= b ==> f contl x)
      ==>
      ?x. a <= x /\ x <= b /\ f x = y``;
