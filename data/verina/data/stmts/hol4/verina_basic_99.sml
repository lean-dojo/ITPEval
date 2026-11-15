(*
  Statement-only formalization of VERINA corpus artifact verina_basic_99,
  catalog title "Triple": the executable integer program uses a branch at 18
  to compute three times its input and satisfies its integer-division
  correctness contract. This file contains no proof.
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
      if x < 18 then
        let a = 2 * x in
        let b = 4 * x in
          (a + b) / 2
      else
        let y = 2 * x in
          x + y``
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
