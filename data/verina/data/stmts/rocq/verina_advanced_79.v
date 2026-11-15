(* Statement-only formalization of VERINA corpus artifact verina_advanced_79,
   catalog title "twoSum": a deterministic executable nested search for the
   lexicographically first pair of increasing indices whose integer entries
   sum to a target, together with its precondition, exact postcondition, and
   final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition twoSum_precond
    (_nums : list Z)
    (_target : Z) : Prop :=
  True.

Fixpoint twoSum_inner
    (x target : Z)
    (lst : list Z)
    (j : nat) : option nat :=
  match lst with
  | [] => None
  | y :: ys =>
      if Z.eqb (x + y) target
      then Some j
      else twoSum_inner x target ys (S j)
  end.

Fixpoint twoSum_outer
    (target : Z)
    (lst : list Z)
    (i : nat) : option (nat * nat) :=
  match lst with
  | [] => None
  | x :: xs =>
      match twoSum_inner x target xs (S i) with
      | Some j => Some (i, j)
      | None => twoSum_outer target xs (S i)
      end
  end.

Definition twoSum
    (nums : list Z)
    (target : Z)
    (_h_precond : twoSum_precond nums target)
    : option (nat * nat) :=
  twoSum_outer target nums 0%nat.

Fixpoint twoSum_pairwise_sum_ne
    (nums : list Z)
    (target : Z) : Prop :=
  match nums with
  | [] => True
  | x :: xs =>
      Forall (fun y => (x + y <> target)%Z) xs /\
      twoSum_pairwise_sum_ne xs target
  end.

Fixpoint twoSum_prefix_clear_from
    (nums prefix : list Z)
    (target : Z)
    (i' : nat) : bool :=
  match prefix with
  | [] => true
  | a :: rest =>
      andb
        (forallb
          (fun b => negb (Z.eqb (a + b) target))
          (skipn (S i') nums))
        (twoSum_prefix_clear_from nums rest target (S i'))
  end.

Definition twoSum_prefix_clear
    (nums : list Z)
    (target : Z)
    (i : nat) : bool :=
  twoSum_prefix_clear_from nums (firstn i nums) target 0%nat.

Definition twoSum_partner_prefix_clear
    (nums : list Z)
    (target : Z)
    (i j : nat) : bool :=
  forallb
    (fun b => negb (Z.eqb (nth i nums 0%Z + b) target))
    (firstn (j - i - 1) (skipn (S i) nums)).

Definition twoSum_postcond
    (nums : list Z)
    (target : Z)
    (result : option (nat * nat))
    (_h_precond : twoSum_precond nums target) : Prop :=
  match result with
  | None => twoSum_pairwise_sum_ne nums target
  | Some ij =>
      let i := fst ij in
      let j := snd ij in
      (i < j)%nat /\
      (j < length nums)%nat /\
      (nth i nums 0%Z + nth j nums 0%Z = target)%Z /\
      twoSum_prefix_clear nums target i = true /\
      twoSum_partner_prefix_clear nums target i j = true
  end.

Theorem twoSum_spec_satisfied
    (nums : list Z)
    (target : Z)
    (h_precond : twoSum_precond nums target) :
  twoSum_postcond
    nums target (twoSum nums target h_precond) h_precond.
Admitted.
