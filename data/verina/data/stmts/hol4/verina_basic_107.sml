(*
  Statement-only formalization of VERINA corpus artifact verina_basic_107,
  catalog title "ComputeAvg": the executable integer program computes the
  floor-divided average of two integers and satisfies its exact Euclidean
  remainder contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val ComputeAvg_precond_def = new_definition (
  "ComputeAvg_precond_def",
  ``ComputeAvg_precond (a : int) (b : int) <=> T``
);

val ComputeAvg_def = new_definition (
  "ComputeAvg_def",
  ``ComputeAvg (a : int) (b : int) =
      (a + b) / 2``
);

val ComputeAvg_postcond_def = new_definition (
  "ComputeAvg_postcond_def",
  ``ComputeAvg_postcond
      (a : int) (b : int) (result : int) <=>
      2 * result = a + b - ((a + b) % 2)``
);

val ComputeAvg_spec_satisfied =
  ``!(a : int) (b : int).
      ComputeAvg_precond a b ==>
      ComputeAvg_postcond a b (ComputeAvg a b)``;
