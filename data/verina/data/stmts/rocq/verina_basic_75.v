(* Statement-only formalization of VERINA corpus artifact verina_basic_75,
   catalog title "minArray": an executable left-to-right scan of a nonempty
   integer array returns its minimum element, together with its precondition,
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition minArray_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Definition minArray_step (current x : Z) : Z :=
  if Z.gtb current x then x else current.

Fixpoint minArray_loop_from
    (remaining : list Z)
    (current : Z) : Z :=
  match remaining with
  | [] => current
  | x :: xs =>
      minArray_loop_from xs (minArray_step current x)
  end.

Definition loop
    (a : list Z)
    (i : nat)
    (current : Z) : Z :=
  minArray_loop_from (skipn i a) current.

Definition minArray
    (a : list Z)
    (_h_precond : minArray_precond a) : Z :=
  loop a 1%nat (nth 0%nat a 0%Z).

Definition minArray_postcond
    (a : list Z)
    (result : Z)
    (_h_precond : minArray_precond a) : Prop :=
  (forall i : nat,
      (i < length a)%nat ->
      (result <= nth i a 0%Z)%Z) /\
  exists i : nat,
    (i < length a)%nat /\
    result = nth i a 0%Z.

Theorem minArray_spec_satisfied
    (a : list Z)
    (h_precond : minArray_precond a) :
  minArray_postcond a (minArray a h_precond) h_precond.
Admitted.
