(* Statement-only formalization of VERINA corpus artifact verina_basic_102,
   catalog title "twoSum": an executable lexicographic search for the first
   pair of increasing array indices whose integer entries sum to a target,
   together with its precondition, postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Fixpoint twoSum_pairwise_target_free
    (nums : list Z)
    (target : Z) : Prop :=
  match nums with
  | [] => True
  | a :: rest =>
      Forall (fun b => (a + b <> target)%Z) rest /\
      twoSum_pairwise_target_free rest target
  end.

Definition twoSum_precond
    (nums : list Z)
    (target : Z) : Prop :=
  (1 < length nums)%nat /\
  ~ twoSum_pairwise_target_free nums target.

Fixpoint twoSum_inner
    (nums : list Z)
    (target : Z)
    (i j fuel : nat) : option (nat * nat) :=
  match fuel with
  | O => None
  | S remaining_fuel =>
      if Z.eqb (nth i nums 0%Z + nth j nums 0%Z) target then
        Some (i, j)
      else
        twoSum_inner nums target i (S j) remaining_fuel
  end.

Fixpoint twoSum_outer
    (nums : list Z)
    (target : Z)
    (i fuel : nat) : option (nat * nat) :=
  match fuel with
  | O => None
  | S remaining_fuel =>
      match twoSum_inner
              nums target i (S i) (length nums - S i) with
      | Some ij => Some ij
      | None =>
          twoSum_outer nums target (S i) remaining_fuel
      end
  end.

Definition twoSum
    (nums : list Z)
    (target : Z)
    (_h_precond : twoSum_precond nums target) : nat * nat :=
  match twoSum_outer nums target 0%nat (length nums - 1) with
  | Some ij => ij
  | None => (0%nat, 0%nat)
  end.

Definition twoSum_postcond
    (nums : list Z)
    (target : Z)
    (result : nat * nat)
    (_h_precond : twoSum_precond nums target) : Prop :=
  let '(i, j) := result in
  (i < j)%nat /\
  (j < length nums)%nat /\
  (nth i nums 0%Z + nth j nums 0%Z = target)%Z /\
  (forall i' j' : nat,
      (i' < i)%nat ->
      (i' < j')%nat ->
      (j' < length nums)%nat ->
      (nth i' nums 0%Z + nth j' nums 0%Z <> target)%Z) /\
  (forall j' : nat,
      (i < j')%nat ->
      (j' < j)%nat ->
      (nth i nums 0%Z + nth j' nums 0%Z <> target)%Z).

Theorem twoSum_spec_satisfied
    (nums : list Z)
    (target : Z)
    (h_precond : twoSum_precond nums target) :
  twoSum_postcond
    nums target (twoSum nums target h_precond) h_precond.
Admitted.
