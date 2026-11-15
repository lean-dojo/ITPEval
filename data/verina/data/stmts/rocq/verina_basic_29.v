(* Statement-only formalization of VERINA corpus artifact verina_basic_29,
   catalog title "removeElement": executable removal of the element at a
   valid index of an integer array, together with the size, unchanged-prefix,
   shifted-suffix postcondition and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Import ListNotations.

Definition removeElement_precond
    (s : list Z) (k : nat) : Prop :=
  (k < length s)%nat.

Fixpoint removeElement_eraseIdx
    (s : list Z) (k : nat) : list Z :=
  match s, k with
  | [], _ => []
  | _ :: rest, O => rest
  | x :: rest, S k' =>
      x :: removeElement_eraseIdx rest k'
  end.

Definition removeElement
    (s : list Z)
    (k : nat)
    (_h_precond : removeElement_precond s k) : list Z :=
  removeElement_eraseIdx s k.

Definition removeElement_postcond
    (s : list Z)
    (k : nat)
    (result : list Z)
    (_h_precond : removeElement_precond s k) : Prop :=
  length result = (length s - 1)%nat /\
  (forall i : nat,
    (i < k)%nat ->
    nth i result 0%Z = nth i s 0%Z) /\
  (forall i : nat,
    (i < length result)%nat ->
    (k <= i)%nat ->
    nth i result 0%Z = nth (i + 1)%nat s 0%Z).

Theorem removeElement_spec_satisfied
    (s : list Z)
    (k : nat)
    (h_precond : removeElement_precond s k) :
  removeElement_postcond
    s k (removeElement s k h_precond) h_precond.
Admitted.
