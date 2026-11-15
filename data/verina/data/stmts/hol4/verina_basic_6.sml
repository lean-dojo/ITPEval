(*
  Statement-only formalization of VERINA corpus artifact verina_basic_6,
  catalog title "minOfThree": the executable comparison program returns one
  of three integers that is less than or equal to every input. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val minOfThree_precond_def = new_definition (
  "minOfThree_precond_def",
  ``minOfThree_precond (a : int) (b : int) (c : int) <=> T``
);

val minOfThree_def = new_definition (
  "minOfThree_def",
  ``minOfThree (a : int) (b : int) (c : int) =
      if a <= b /\ a <= c then
        a
      else if b <= a /\ b <= c then
        b
      else
        c``
);

val minOfThree_postcond_def = new_definition (
  "minOfThree_postcond_def",
  ``minOfThree_postcond
      (a : int) (b : int) (c : int) (result : int) <=>
      (result <= a /\ result <= b /\ result <= c) /\
      (result = a \/ result = b \/ result = c)``
);

val minOfThree_spec_satisfied =
  ``!(a : int) (b : int) (c : int).
      minOfThree_precond a b c ==>
      minOfThree_postcond a b c (minOfThree a b c)``;
