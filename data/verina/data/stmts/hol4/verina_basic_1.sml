(*
  Statement-only formalization of VERINA corpus artifact verina_basic_1,
  catalog title "hasOppositeSign": the executable integer-product sign test
  returns whether two integers have opposite signs and satisfies its Boolean
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val hasOppositeSign_precond_def = new_definition (
  "hasOppositeSign_precond_def",
  ``hasOppositeSign_precond (a : int) (b : int) <=> T``
);

val hasOppositeSign_def = new_definition (
  "hasOppositeSign_def",
  ``hasOppositeSign (a : int) (b : int) = (a * b < 0)``
);

val hasOppositeSign_postcond_def = new_definition (
  "hasOppositeSign_postcond_def",
  ``hasOppositeSign_postcond
      (a : int) (b : int) (result : bool) <=>
      (((a < 0 /\ b > 0) \/ (a > 0 /\ b < 0)) ==> result) /\
      (~((a < 0 /\ b > 0) \/ (a > 0 /\ b < 0)) ==> ~result)``
);

val hasOppositeSign_spec_satisfied =
  ``!(a : int) (b : int).
      hasOppositeSign_precond a b ==>
      hasOppositeSign_postcond a b (hasOppositeSign a b)``;
