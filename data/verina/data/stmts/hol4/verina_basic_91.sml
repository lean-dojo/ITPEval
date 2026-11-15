(*
  Statement-only formalization of VERINA corpus artifact verina_basic_91,
  catalog title "Swap": the executable integer-pair program exchanges its two
  inputs and satisfies the exact swap and changed-position postcondition.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val Swap_precond_def = new_definition (
  "Swap_precond_def",
  ``Swap_precond (X : int) (Y : int) <=> T``
);

val Swap_def = new_definition (
  "Swap_def",
  ``Swap (X : int) (Y : int) =
      let x = X in
      let y = Y in
      let tmp = x in
      let x = y in
      let y = tmp in
        (x,y)``
);

val Swap_postcond_def = new_definition (
  "Swap_postcond_def",
  ``Swap_postcond
      (X : int) (Y : int) (result : int # int) <=>
      FST result = Y /\
      SND result = X /\
      (X <> Y ==> FST result <> X /\ SND result <> Y)``
);

val Swap_spec_satisfied =
  ``!(X : int) (Y : int).
      Swap_precond X Y ==>
      Swap_postcond X Y (Swap X Y)``;
