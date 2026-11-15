(* Statement-only formalization of VERINA corpus artifact verina_advanced_80,
   catalog title "twoSum": an exact fuel-bounded executable search for two
   increasing array indices whose integer entries sum to a target, together
   with the unique-solution precondition, result postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition twoSum_precond
    (nums : list Z)
    (target : Z) : Prop :=
  (2 <= length nums)%nat /\
  existsb
    (fun i =>
      existsb
        (fun j =>
          Z.eqb (nth i nums 0%Z + nth j nums 0%Z) target)
        (seq 0 i))
    (seq 0 (length nums)) = true /\
  length
    (flat_map
      (fun i =>
        filter
          (fun j =>
            Z.eqb (nth i nums 0%Z + nth j nums 0%Z) target)
          (seq 0 i))
      (seq 0 (length nums))) = 1%nat.

Fixpoint twoSum_findIndices
    (nums : list Z)
    (target : Z)
    (i j fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S remaining_fuel =>
      if Nat.leb (length nums) i then
        []
      else if Nat.leb (length nums) j then
        twoSum_findIndices nums target
          (S i) (i + 2) remaining_fuel
      else if Z.eqb
                (nth i nums 0%Z + nth j nums 0%Z)
                target then
        [i; j]
      else
        twoSum_findIndices nums target
          i (S j) remaining_fuel
  end.

Definition twoSum
    (nums : list Z)
    (target : Z)
    (_h_precond : twoSum_precond nums target) : list nat :=
  twoSum_findIndices nums target
    0%nat 1%nat (length nums * length nums).

Definition twoSum_postcond
    (nums : list Z)
    (target : Z)
    (result : list nat)
    (_h_precond : twoSum_precond nums target) : Prop :=
  length result = 2%nat /\
  (nth 0 result 0 < length nums)%nat /\
  (nth 1 result 0 < length nums)%nat /\
  (nth 0 result 0 < nth 1 result 0)%nat /\
  (nth (nth 0%nat result 0%nat) nums 0%Z +
     nth (nth 1%nat result 0%nat) nums 0%Z = target)%Z.

Theorem twoSum_spec_satisfied
    (nums : list Z)
    (target : Z)
    (h_precond : twoSum_precond nums target) :
  twoSum_postcond
    nums target (twoSum nums target h_precond) h_precond.
Admitted.
