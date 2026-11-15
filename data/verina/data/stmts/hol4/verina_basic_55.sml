(*
  Statement-only formalization of VERINA corpus artifact verina_basic_55,
  catalog title "Compare": the executable Boolean equality test on two
  integers returns true exactly when they are equal and satisfies its
  precondition/postcondition correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val Compare_precond_def = new_definition (
  "Compare_precond_def",
  ``Compare_precond (a : int) (b : int) <=> T``
);

val Compare_def = new_definition (
  "Compare_def",
  ``Compare (a : int) (b : int) =
      if a = b then T else F``
);

val Compare_postcond_def = new_definition (
  "Compare_postcond_def",
  ``Compare_postcond
      (a : int) (b : int) (result : bool) <=>
      (a = b ==> result = T) /\
      (~(a = b) ==> result = F)``
);

val Compare_spec_satisfied =
  ``!(a : int) (b : int).
      Compare_precond a b ==>
      Compare_postcond a b (Compare a b)``;
