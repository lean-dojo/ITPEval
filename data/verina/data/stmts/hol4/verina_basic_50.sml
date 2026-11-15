(*
  Statement-only formalization of VERINA corpus artifact verina_basic_50,
  catalog title "Abs": the total executable integer program returns its input
  when nonnegative and its additive inverse when negative, under the stated
  two-branch correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val Abs_precond_def = new_definition (
  "Abs_precond_def",
  ``Abs_precond (x : int) <=> T``
);

val Abs_def = new_definition (
  "Abs_def",
  ``Abs (x : int) =
      if x < 0 then 0 - x else x``
);

val Abs_postcond_def = new_definition (
  "Abs_postcond_def",
  ``Abs_postcond (x : int) (result : int) <=>
      (0 <= x ==> x = result) /\
      (x < 0 ==> x + result = 0)``
);

val Abs_spec_satisfied =
  ``!x : int.
      Abs_precond x ==>
      Abs_postcond x (Abs x)``;
