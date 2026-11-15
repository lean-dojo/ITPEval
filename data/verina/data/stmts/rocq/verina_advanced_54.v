(* Statement-only formalization of VERINA corpus artifact verina_advanced_54,
   catalog title "missingNumber": an executable triangular-sum computation of
   the unique missing natural number from a duplicate-free list bounded by its
   length, together with its exact range-and-membership correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition missingNumber_precond
    (nums : list nat) : Prop :=
  forallb
    (fun x => Nat.leb x (length nums))
    nums = true /\
  NoDup nums.

Definition missingNumber
    (nums : list nat)
    (_h_precond : missingNumber_precond nums) : nat :=
  let n := length nums in
  let expectedSum :=
    Nat.div (Nat.mul n (Nat.add n 1%nat)) 2%nat in
  let actualSum :=
    fold_left Nat.add nums 0%nat in
  Nat.sub expectedSum actualSum.

Definition missingNumber_postcond
    (nums : list nat)
    (result : nat)
    (_h_precond : missingNumber_precond nums) : Prop :=
  let n := length nums in
  In result (seq 0%nat (Nat.add n 1%nat)) /\
  ~ In result nums /\
  forall x : nat,
    In x (seq 0%nat (Nat.add n 1%nat)) ->
    x <> result ->
    In x nums.

Theorem missingNumber_spec_satisfied
    (nums : list nat)
    (h_precond : missingNumber_precond nums) :
  missingNumber_postcond
    nums (missingNumber nums h_precond) h_precond.
Admitted.
