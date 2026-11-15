(* Statement-only formalization of VERINA corpus artifact verina_advanced_63,
   catalog title "removeDuplicates": an executable scan that counts the
   distinct values in a nondecreasing integer list, together with its exact
   duplicate-erasure length correctness contract. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Sorting.Sorted ZArith.

Import ListNotations.

Definition removeDuplicates_precond (nums : list Z) : Prop :=
  StronglySorted Z.le nums.

Fixpoint removeDuplicates_countUniques
    (prev : Z)
    (xs : list Z)
    (k : nat) : nat :=
  match xs with
  | [] => k
  | head :: tail =>
      if Z.eqb head prev
      then removeDuplicates_countUniques prev tail k
      else
        let newK := Nat.add k 1%nat in
        removeDuplicates_countUniques head tail newK
  end.

Definition removeDuplicates
    (nums : list Z)
    (_h_precond : removeDuplicates_precond nums) : nat :=
  match nums with
  | [] => 0%nat
  | h :: t =>
      let init := h in
      let initCount := 1%nat in
      removeDuplicates_countUniques init t initCount
  end.

Definition removeDuplicates_eraseDups
    (nums : list Z) : list Z :=
  nodup Z.eq_dec nums.

Definition removeDuplicates_postcond
    (nums : list Z)
    (result : nat)
    (_h_precond : removeDuplicates_precond nums) : Prop :=
  Nat.sub result (length (removeDuplicates_eraseDups nums)) = 0%nat /\
  Nat.le (length (removeDuplicates_eraseDups nums)) result.

Theorem removeDuplicates_spec_satisfied
    (nums : list Z)
    (h_precond : removeDuplicates_precond nums) :
  removeDuplicates_postcond
    nums (removeDuplicates nums h_precond) h_precond.
Admitted.
