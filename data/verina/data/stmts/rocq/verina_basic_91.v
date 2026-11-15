(* Statement-only formalization of VERINA corpus artifact verina_basic_91,
   catalog title "Swap": executable swapping of two arbitrary integers,
   together with its unconditional precondition, postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import ZArith.

Definition Swap_precond (_X _Y : Z) : Prop :=
  True.

Definition Swap
    (X Y : Z)
    (_h_precond : Swap_precond X Y) : Z * Z :=
  let x := X in
  let y := Y in
  let tmp := x in
  let x := y in
  let y := tmp in
  (x, y).

Definition Swap_postcond
    (X Y : Z)
    (result : Z * Z)
    (_h_precond : Swap_precond X Y) : Prop :=
  fst result = Y /\
  snd result = X /\
  (X <> Y -> fst result <> X /\ snd result <> Y).

Theorem Swap_spec_satisfied
    (X Y : Z)
    (h_precond : Swap_precond X Y) :
  Swap_postcond X Y (Swap X Y h_precond) h_precond.
Admitted.
