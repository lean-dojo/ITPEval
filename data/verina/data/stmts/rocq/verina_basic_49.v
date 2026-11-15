(* Statement-only formalization of VERINA corpus artifact verina_basic_49,
   catalog title "findFirstOdd": an executable left-to-right search of a
   nonempty integer array for its first odd element, returning its natural
   index as an option, together with its exact first-occurrence postcondition
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition isOdd (x : Z) : bool :=
  negb (Z.eqb (Z.modulo x 2) 0).

Definition findFirstOdd_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Fixpoint findFirstOdd_from
    (a : list Z)
    (index : nat) : option nat :=
  match a with
  | [] => None
  | x :: rest =>
      if isOdd x
      then Some index
      else findFirstOdd_from rest (S index)
  end.

Definition findFirstOdd
    (a : list Z)
    (_h_precond : findFirstOdd_precond a) : option nat :=
  findFirstOdd_from a 0%nat.

Definition findFirstOdd_postcond
    (a : list Z)
    (result : option nat)
    (_h_precond : findFirstOdd_precond a) : Prop :=
  match result with
  | Some index =>
      (index < length a)%nat /\
      isOdd (nth index a 0) = true /\
      forall j : nat,
        (j < index)%nat ->
        isOdd (nth j a 0) <> true
  | None =>
      forall i : nat,
        (i < length a)%nat ->
        isOdd (nth i a 0) <> true
  end.

Theorem findFirstOdd_spec_satisfied
    (a : list Z)
    (h_precond : findFirstOdd_precond a) :
  findFirstOdd_postcond
    a (findFirstOdd a h_precond) h_precond.
Admitted.
