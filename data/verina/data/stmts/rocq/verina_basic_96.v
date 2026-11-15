(* Statement-only formalization of VERINA corpus artifact verina_basic_96,
   catalog title "SwapSimultaneous": executable simultaneous swapping of two
   arbitrary integers, together with its unconditional precondition,
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import ZArith.

Definition SwapSimultaneous_precond (_X _Y : Z) : Prop :=
  True.

Definition SwapSimultaneous
    (X Y : Z)
    (_h_precond : SwapSimultaneous_precond X Y) : Z * Z :=
  (Y, X).

Definition SwapSimultaneous_postcond
    (X Y : Z)
    (result : Z * Z)
    (_h_precond : SwapSimultaneous_precond X Y) : Prop :=
  fst result = Y /\
  snd result = X /\
  (X <> Y -> fst result <> X /\ snd result <> Y).

Theorem SwapSimultaneous_spec_satisfied
    (X Y : Z)
    (h_precond : SwapSimultaneous_precond X Y) :
  SwapSimultaneous_postcond
    X Y (SwapSimultaneous X Y h_precond) h_precond.
Admitted.
