(* Statement-only formalization of VERINA corpus artifact verina_basic_12,
   catalog title "cubeSurfaceArea": an executable natural-number computation
   of a cube's surface area from its edge length, together with its
   precondition, postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Definition cubeSurfaceArea_precond (_size : nat) : Prop :=
  True.

Definition cubeSurfaceArea
    (size : nat)
    (_h_precond : cubeSurfaceArea_precond size) : nat :=
  6 * size * size.

Definition cubeSurfaceArea_postcond
    (size result : nat)
    (_h_precond : cubeSurfaceArea_precond size) : Prop :=
  Nat.sub result (6 * size * size) = 0 /\
  Nat.sub (6 * size * size) result = 0.

Theorem cubeSurfaceArea_spec_satisfied
    (size : nat)
    (h_precond : cubeSurfaceArea_precond size) :
  cubeSurfaceArea_postcond
    size (cubeSurfaceArea size h_precond) h_precond.
Admitted.
