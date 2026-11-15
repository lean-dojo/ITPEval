(* Statement-only formalization of VERINA corpus artifact verina_advanced_78,
   catalog title "twoSum": a deterministic executable search for the unique
   pair of increasing indices whose integer entries sum to a target, together
   with its precondition, postcondition, and final correctness proposition.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition twoSum_pairwise_sums (nums : list Z) : list Z :=
  flat_map
    (fun i =>
      map
        (fun y => (nth i nums 0%Z + y)%Z)
        (skipn (i + 1) nums))
    (seq 0 (length nums)).

Definition twoSum_precond
    (nums : list Z) (target : Z) : Prop :=
  (1 < length nums)%nat /\
  count_occ Z.eq_dec (twoSum_pairwise_sums nums) target = 1%nat.

Fixpoint findComplement_from
    (nums : list Z)
    (target : Z)
    (i : nat)
    (x : Z)
    (j : nat) : option nat :=
  match nums with
  | [] => None
  | y :: ys =>
      if Z.eqb (x + y) target
      then Some (i + j + 1)%nat
      else findComplement_from ys target i x (S j)
  end.

Definition findComplement
    (nums : list Z)
    (target : Z)
    (i : nat)
    (x : Z) : option nat :=
  findComplement_from nums target i x 0%nat.

Fixpoint twoSumAux
    (nums : list Z)
    (target : Z)
    (i : nat) : nat * nat :=
  match nums with
  | [] => (0%nat, 0%nat)
  | x :: xs =>
      match findComplement xs target i x with
      | Some j => (i, j)
      | None => twoSumAux xs target (S i)
      end
  end.

Definition twoSum
    (nums : list Z)
    (target : Z)
    (_h_precond : twoSum_precond nums target) : nat * nat :=
  twoSumAux nums target 0%nat.

Definition twoSum_postcond
    (nums : list Z)
    (target : Z)
    (result : nat * nat)
    (_h_precond : twoSum_precond nums target) : Prop :=
  let i := fst result in
  let j := snd result in
  (i < j)%nat /\
  (i < length nums)%nat /\
  (j < length nums)%nat /\
  (nth i nums 0%Z + nth j nums 0%Z = target)%Z.

Theorem twoSum_spec_satisfied
    (nums : list Z)
    (target : Z)
    (h_precond : twoSum_precond nums target) :
  twoSum_postcond
    nums target (twoSum nums target h_precond) h_precond.
Admitted.
