(*
  Statement-only formalization of VERINA artifact verina_advanced_41,
  cataloged as "maxOfThree": the executable comparison program returns one
  of three integers that is greater than or equal to every input. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val maxOfThree_precond_def = new_definition (
  "maxOfThree_precond_def",
  ``maxOfThree_precond (a : int) (b : int) (c : int) <=> T``
);

val maxOfThree_def = new_definition (
  "maxOfThree_def",
  ``maxOfThree (a : int) (b : int) (c : int) =
      if a >= b /\ a >= c then
        a
      else if b >= a /\ b >= c then
        b
      else
        c``
);

val maxOfThree_postcond_def = new_definition (
  "maxOfThree_postcond_def",
  ``maxOfThree_postcond
      (a : int) (b : int) (c : int) (result : int) <=>
      (result >= a /\ result >= b /\ result >= c) /\
      (result = a \/ result = b \/ result = c)``
);

val maxOfThree_spec_satisfied =
  ``!(a : int) (b : int) (c : int).
      maxOfThree_precond a b c ==>
      maxOfThree_postcond a b c (maxOfThree a b c)``;
