(*
  Statement-only formalization of VERINA corpus artifact verina_basic_98,
  catalog title "Triple": the total executable integer program multiplies its
  input by 3 and satisfies its integer-division correctness contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val Triple_precond_def = new_definition (
  "Triple_precond_def",
  ``Triple_precond (x : int) <=> T``
);

val Triple_def = new_definition (
  "Triple_def",
  ``Triple (x : int) = x * 3``
);

val Triple_postcond_def = new_definition (
  "Triple_postcond_def",
  ``Triple_postcond (x : int) (result : int) <=>
      result / 3 = x /\
      result / 3 * 3 = result``
);

val Triple_spec_satisfied =
  ``!x : int.
      Triple_precond x ==>
      Triple_postcond x (Triple x)``;
