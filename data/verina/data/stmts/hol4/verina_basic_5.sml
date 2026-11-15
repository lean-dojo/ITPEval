(*
  Statement-only formalization of VERINA corpus artifact verina_basic_5,
  catalog title "multiply": the total executable integer multiplication
  program returns the product of its two inputs and satisfies the stated
  two-sided subtraction correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val multiply_precond_def = new_definition (
  "multiply_precond_def",
  ``multiply_precond (a : int) (b : int) <=> T``
);

val multiply_def = new_definition (
  "multiply_def",
  ``multiply (a : int) (b : int) = a * b``
);

val multiply_postcond_def = new_definition (
  "multiply_postcond_def",
  ``multiply_postcond (a : int) (b : int) (result : int) <=>
      result - a * b = 0 /\ a * b - result = 0``
);

val multiply_spec_satisfied =
  ``!(a : int) (b : int).
      multiply_precond a b ==>
      multiply_postcond a b (multiply a b)``;
