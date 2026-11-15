(*
  Statement-only formalization of VERINA corpus artifact verina_basic_13,
  catalog title "cubeElements": the executable integer-array map replaces
  every element by its cube and satisfies the length and pointwise cube
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val cubeElements_precond_def = new_definition (
  "cubeElements_precond_def",
  ``cubeElements_precond (a : int list) <=> T``
);

val cubeElements_def = new_definition (
  "cubeElements_def",
  ``cubeElements (a : int list) =
      MAP (\x : int. x * x * x) a``
);

val cubeElements_postcond_def = new_definition (
  "cubeElements_postcond_def",
  ``cubeElements_postcond
      (a : int list) (result : int list) <=>
      LENGTH result = LENGTH a /\
      (!i : num.
         i < LENGTH a ==>
         EL i result = EL i a * EL i a * EL i a)``
);

val cubeElements_spec_satisfied =
  ``!a : int list.
      cubeElements_precond a ==>
      cubeElements_postcond a (cubeElements a)``;
