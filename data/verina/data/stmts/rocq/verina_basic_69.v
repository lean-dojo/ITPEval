(* Statement-only formalization of VERINA corpus artifact verina_basic_69,
   catalog title "LinearSearch": executable left-to-right search for the first
   occurrence of an integer in an integer array under an existence
   precondition, together with its helper computation, first-occurrence
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition LinearSearch_precond
    (a : list Z) (e : Z) : Prop :=
  exists i : nat,
    (i < length a)%nat /\
    nth i a 0%Z = e.

Fixpoint linearSearchAux_from
    (remaining : list Z) (e : Z) (n : nat) : nat :=
  match remaining with
  | [] => 0%nat
  | x :: rest =>
      if Z.eqb x e
      then n
      else linearSearchAux_from rest e (S n)
  end.

Definition linearSearchAux
    (a : list Z) (e : Z) (n : nat) : nat :=
  linearSearchAux_from (skipn n a) e n.

Definition LinearSearch
    (a : list Z)
    (e : Z)
    (_h_precond : LinearSearch_precond a e) : nat :=
  linearSearchAux a e 0%nat.

Definition LinearSearch_postcond
    (a : list Z)
    (e : Z)
    (result : nat)
    (_h_precond : LinearSearch_precond a e) : Prop :=
  (result < length a)%nat /\
  nth result a 0%Z = e /\
  forall k : nat,
    (k < result)%nat ->
    nth k a 0%Z <> e.

Theorem LinearSearch_spec_satisfied
    (a : list Z)
    (e : Z)
    (h_precond : LinearSearch_precond a e) :
  LinearSearch_postcond
    a e (LinearSearch a e h_precond) h_precond.
Admitted.
