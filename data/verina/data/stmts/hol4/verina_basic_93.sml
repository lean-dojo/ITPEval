(*
  Statement-only formalization of VERINA corpus artifact verina_basic_93,
  catalog title "SwapBitvectors": the executable 8-bit word program swaps
  its two inputs through the specified three bitwise-XOR steps and satisfies
  the exact swap and changed-position postcondition. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory;

val SwapBitvectors_precond_def = new_definition (
  "SwapBitvectors_precond_def",
  ``SwapBitvectors_precond (X : word8) (Y : word8) <=> T``
);

val SwapBitvectors_def = new_definition (
  "SwapBitvectors_def",
  ``SwapBitvectors (X : word8) (Y : word8) =
      let temp = X ?? Y in
      let newY = temp ?? Y in
      let newX = temp ?? newY in
        (newX, newY)``
);

val SwapBitvectors_postcond_def = new_definition (
  "SwapBitvectors_postcond_def",
  ``SwapBitvectors_postcond
      (X : word8) (Y : word8) (result : word8 # word8) <=>
      FST result = Y /\
      SND result = X /\
      (X <> Y ==> FST result <> X /\ SND result <> Y)``
);

val SwapBitvectors_spec_satisfied =
  ``!(X : word8) (Y : word8).
      SwapBitvectors_precond X Y ==>
      SwapBitvectors_postcond X Y (SwapBitvectors X Y)``;
