(* Statement-only formalization of VERINA corpus artifact verina_basic_74,
   catalog title "maxArray": an executable left-to-right scan of a nonempty
   integer array returns its maximum element, together with its precondition,
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition maxArray_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Definition maxArray_step (current x : Z) : Z :=
  if Z.gtb current x then current else x.

Fixpoint maxArray_aux_from
    (remaining : list Z)
    (current : Z) : Z :=
  match remaining with
  | [] => current
  | x :: xs =>
      maxArray_aux_from xs (maxArray_step current x)
  end.

Definition maxArray_aux
    (a : list Z)
    (index : nat)
    (current : Z) : Z :=
  maxArray_aux_from (skipn index a) current.

Definition maxArray
    (a : list Z)
    (_h_precond : maxArray_precond a) : Z :=
  maxArray_aux a 1%nat (nth 0%nat a 0%Z).

Definition maxArray_postcond
    (a : list Z)
    (result : Z)
    (_h_precond : maxArray_precond a) : Prop :=
  (forall k : nat,
      (k < length a)%nat ->
      (nth k a 0%Z <= result)%Z) /\
  exists k : nat,
    (k < length a)%nat /\
    result = nth k a 0%Z.

Theorem maxArray_spec_satisfied
    (a : list Z)
    (h_precond : maxArray_precond a) :
  maxArray_postcond a (maxArray a h_precond) h_precond.
Admitted.
