(* Statement-only formalization of VERINA corpus artifact verina_basic_62,
   catalog title "Find": an executable left-to-right search for the first
   occurrence of an integer in an integer array, returning its zero-based
   index or -1, together with the full correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition Find_precond (_a : list Z) (_key : Z) : Prop :=
  True.

Fixpoint Find_search
    (remaining : list Z) (key : Z) (index : nat) : Z :=
  match remaining with
  | [] => -1
  | x :: rest =>
      if Z.eqb x key
      then Z.of_nat index
      else Find_search rest key (S index)
  end.

Definition Find
    (a : list Z)
    (key : Z)
    (_h_precond : Find_precond a key) : Z :=
  Find_search a key 0%nat.

Definition Find_postcond
    (a : list Z)
    (key result : Z)
    (_h_precond : Find_precond a key) : Prop :=
  (result = -1 \/
    (0 <= result /\ result < Z.of_nat (length a))) /\
  (result <> -1 ->
    nth (Z.to_nat result) a 0 = key /\
    forall i : nat,
      (i < Z.to_nat result)%nat ->
      nth i a 0 <> key) /\
  (result = -1 ->
    forall i : nat,
      (i < length a)%nat ->
      nth i a 0 <> key).

Theorem Find_spec_satisfied
    (a : list Z)
    (key : Z)
    (h_precond : Find_precond a key) :
  Find_postcond a key (Find a key h_precond) h_precond.
Admitted.
