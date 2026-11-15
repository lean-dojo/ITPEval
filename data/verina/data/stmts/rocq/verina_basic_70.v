(* Statement-only formalization of VERINA corpus artifact verina_basic_70,
   catalog title "LinearSearch3": executable left-to-right search of an
   integer array for the first element satisfying a Boolean predicate under
   an existence precondition, together with its first-occurrence
   postcondition and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition LinearSearch3_precond
    (a : list Z) (P : Z -> bool) : Prop :=
  exists i : nat,
    (i < length a)%nat /\
    P (nth i a 0%Z) = true.

Fixpoint LinearSearch3_scan
    (remaining : list Z)
    (P : Z -> bool)
    (n : nat) : nat :=
  match remaining with
  | [] => 0%nat
  | x :: rest =>
      if P x
      then n
      else LinearSearch3_scan rest P (S n)
  end.

Definition LinearSearch3_loop
    (a : list Z)
    (P : Z -> bool)
    (n : nat) : nat :=
  LinearSearch3_scan (skipn n a) P n.

Definition LinearSearch3
    (a : list Z)
    (P : Z -> bool)
    (_h_precond : LinearSearch3_precond a P) : nat :=
  LinearSearch3_loop a P 0%nat.

Definition LinearSearch3_postcond
    (a : list Z)
    (P : Z -> bool)
    (result : nat)
    (_h_precond : LinearSearch3_precond a P) : Prop :=
  (result < length a)%nat /\
  P (nth result a 0%Z) = true /\
  forall k : nat,
    (k < result)%nat ->
    P (nth k a 0%Z) <> true.

Theorem LinearSearch3_spec_satisfied
    (a : list Z)
    (P : Z -> bool)
    (h_precond : LinearSearch3_precond a P) :
  LinearSearch3_postcond
    a P (LinearSearch3 a P h_precond) h_precond.
Admitted.
