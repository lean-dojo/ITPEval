(* Statement-only formalization of VERINA corpus artifact verina_basic_82,
   catalog title "remove_front": executable removal of the first element from
   a nonempty integer array by copying its remaining suffix into a fresh
   array, together with its helper, precondition, postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition remove_front_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Fixpoint copyFrom_remaining
    (remaining acc : list Z) : list Z :=
  match remaining with
  | [] => acc
  | x :: rest =>
      copyFrom_remaining rest (acc ++ [x])
  end.

Definition copyFrom
    (a : list Z)
    (i : nat)
    (acc : list Z) : list Z :=
  copyFrom_remaining (skipn i a) acc.

Definition remove_front
    (a : list Z)
    (_h_precond : remove_front_precond a) : list Z :=
  if Nat.ltb 0%nat (length a)
  then copyFrom a 1%nat []
  else [].

Definition remove_front_postcond
    (a result : list Z)
    (_h_precond : remove_front_precond a) : Prop :=
  (0 < length a)%nat /\
  length result = (length a - 1)%nat /\
  forall i : nat,
    (i < length result)%nat ->
    nth i result 0%Z = nth (i + 1)%nat a 0%Z.

Theorem remove_front_spec_satisfied
    (a : list Z)
    (h_precond : remove_front_precond a) :
  remove_front_postcond
    a (remove_front a h_precond) h_precond.
Admitted.
