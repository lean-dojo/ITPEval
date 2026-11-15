(* Statement-only formalization of VERINA corpus artifact verina_basic_68,
   catalog title "LinearSearch": executable left-to-right search for the first
   occurrence of an integer in an integer array, returning its index or the
   array size, together with its trivial precondition, first-occurrence
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition LinearSearch_precond
    (_a : list Z) (_e : Z) : Prop :=
  True.

Fixpoint LinearSearch_scan
    (remaining : list Z) (e : Z) (n : nat) : nat :=
  match remaining with
  | [] => n
  | x :: rest =>
      if Z.eqb x e
      then n
      else LinearSearch_scan rest e (S n)
  end.

Definition LinearSearch_loop
    (a : list Z) (e : Z) (n : nat) : nat :=
  LinearSearch_scan (skipn n a) e n.

Definition LinearSearch
    (a : list Z)
    (e : Z)
    (_h_precond : LinearSearch_precond a e) : nat :=
  LinearSearch_loop a e 0%nat.

Definition LinearSearch_postcond
    (a : list Z)
    (e : Z)
    (result : nat)
    (_h_precond : LinearSearch_precond a e) : Prop :=
  Nat.le result (length a) /\
  (result = length a \/ nth result a 0%Z = e) /\
  (forall i : nat,
    (i < result)%nat ->
    nth i a 0%Z <> e).

Theorem LinearSearch_spec_satisfied
    (a : list Z)
    (e : Z)
    (h_precond : LinearSearch_precond a e) :
  LinearSearch_postcond
    a e (LinearSearch a e h_precond) h_precond.
Admitted.
