(*
  Statement-only formalization of VERINA corpus artifact verina_basic_96,
  catalog title "SwapSimultaneous": the executable integer-pair program
  simultaneously exchanges its two inputs and satisfies the exact swap and
  changed-position postcondition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val SwapSimultaneous_precond_def = new_definition (
  "SwapSimultaneous_precond_def",
  ``SwapSimultaneous_precond (X : int) (Y : int) <=> T``
);

val SwapSimultaneous_def = new_definition (
  "SwapSimultaneous_def",
  ``SwapSimultaneous (X : int) (Y : int) = (Y, X)``
);

val SwapSimultaneous_postcond_def = new_definition (
  "SwapSimultaneous_postcond_def",
  ``SwapSimultaneous_postcond
      (X : int) (Y : int) (result : int # int) <=>
      FST result = Y /\
      SND result = X /\
      (X <> Y ==> FST result <> X /\ SND result <> Y)``
);

val SwapSimultaneous_spec_satisfied =
  ``!(X : int) (Y : int).
      SwapSimultaneous_precond X Y ==>
      SwapSimultaneous_postcond X Y (SwapSimultaneous X Y)``;
