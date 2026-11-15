(*
  Statement-only formalization of VERINA corpus artifact verina_basic_101,
  catalog title "Triple": the executable integer program doubles its input,
  adds the original input, and satisfies its integer-division correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val Triple_precond_def = new_definition (
  "Triple_precond_def",
  ``Triple_precond (x : int) <=> T``
);

val Triple_def = new_definition (
  "Triple_def",
  ``Triple (x : int) =
      let y = x * 2 in
        y + x``
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
