(* Statement-only formalization of VERINA corpus artifact verina_advanced_69,
   catalog title "searchInsert": executable search for the insertion index of
   an integer in a strictly increasing integer list, together with its bounds
   and ordering correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Sorting.Sorted
  ZArith.

Import ListNotations.

Definition searchInsert_precond
    (xs : list Z) (_target : Z) : Prop :=
  StronglySorted Z.lt xs.

Fixpoint searchInsert_helper
    (ys : list Z) (target : Z) (idx : nat) : nat :=
  match ys with
  | [] => idx
  | y :: ys' =>
      if Z.leb target y
      then idx
      else searchInsert_helper ys' target (S idx)
  end.

Definition searchInsert
    (xs : list Z)
    (target : Z)
    (_h_precond : searchInsert_precond xs target) : nat :=
  match xs with
  | [] => 0%nat
  | _ :: _ => searchInsert_helper xs target 0%nat
  end.

Definition searchInsert_postcond
    (xs : list Z)
    (target : Z)
    (result : nat)
    (_h_precond : searchInsert_precond xs target) : Prop :=
  let allBeforeLess :=
    forallb
      (fun i => Z.ltb (nth i xs 0%Z) target)
      (seq 0%nat result) in
  let inBounds := Nat.le result (length xs) in
  let insertedCorrectly :=
    Nat.lt result (length xs) ->
    Z.le target (nth result xs 0%Z) in
  inBounds /\ allBeforeLess = true /\ insertedCorrectly.

Theorem searchInsert_spec_satisfied
    (xs : list Z)
    (target : Z)
    (h_precond : searchInsert_precond xs target) :
  searchInsert_postcond
    xs target (searchInsert xs target h_precond) h_precond.
Admitted.
