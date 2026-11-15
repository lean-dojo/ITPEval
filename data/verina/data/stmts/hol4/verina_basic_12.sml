(*
  Statement-only formalization of VERINA corpus artifact verina_basic_12,
  catalog title "cubeSurfaceArea": the executable natural-number program
  computes six times the square of a cube's edge length and satisfies its
  two-sided truncated-subtraction correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val cubeSurfaceArea_precond_def = new_definition (
  "cubeSurfaceArea_precond_def",
  ``cubeSurfaceArea_precond (size : num) <=> T``
);

val cubeSurfaceArea_def = new_definition (
  "cubeSurfaceArea_def",
  ``cubeSurfaceArea (size : num) = 6 * size * size``
);

val cubeSurfaceArea_postcond_def = new_definition (
  "cubeSurfaceArea_postcond_def",
  ``cubeSurfaceArea_postcond (size : num) (result : num) <=>
      result - 6 * size * size = 0 /\
      6 * size * size - result = 0``
);

val cubeSurfaceArea_spec_satisfied =
  ``!size : num.
      cubeSurfaceArea_precond size ==>
      cubeSurfaceArea_postcond size (cubeSurfaceArea size)``;
