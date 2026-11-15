(*
  Statement-only formalization of VERINA corpus artifact verina_basic_92,
  catalog title "SwapArithmetic": the executable integer-pair program swaps
  its two inputs through the specified subtraction and addition steps and
  satisfies the exact swap and changed-position postcondition. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val SwapArithmetic_precond_def = new_definition (
  "SwapArithmetic_precond_def",
  ``SwapArithmetic_precond (X : int) (Y : int) <=> T``
);

val SwapArithmetic_def = new_definition (
  "SwapArithmetic_def",
  ``SwapArithmetic (X : int) (Y : int) =
      let x1 = X in
      let y1 = Y in
      let x2 = y1 - x1 in
      let y2 = y1 - x2 in
      let x3 = y2 + x2 in
        (x3, y2)``
);

val SwapArithmetic_postcond_def = new_definition (
  "SwapArithmetic_postcond_def",
  ``SwapArithmetic_postcond
      (X : int) (Y : int) (result : int # int) <=>
      FST result = Y /\
      SND result = X /\
      (X <> Y ==> FST result <> X /\ SND result <> Y)``
);

val SwapArithmetic_spec_satisfied =
  ``!(X : int) (Y : int).
      SwapArithmetic_precond X Y ==>
      SwapArithmetic_postcond X Y (SwapArithmetic X Y)``;
