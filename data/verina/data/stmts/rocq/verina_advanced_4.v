(* Statement-only formalization of VERINA corpus artifact verina_advanced_4,
   catalog title "LongestIncreasingSubsequence": an executable dynamic-
   programming computation of the longest strictly increasing subsequence
   length of an integer array, together with its exhaustive-subsequence
   maximality contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition LongestIncreasingSubsequence_precond
    (_a : list Z) : Prop :=
  True.

Definition intMax (x y : Z) : Z :=
  if Z.ltb x y then y else x.

Definition LongestIncreasingSubsequence_get
    (xs : list Z) (index : nat) : Z :=
  nth index xs 0.

Fixpoint LongestIncreasingSubsequence_set
    (index : nat) (value : Z) (xs : list Z) : list Z :=
  match index, xs with
  | 0%nat, _ :: rest => value :: rest
  | S index', x :: rest =>
      x :: LongestIncreasingSubsequence_set index' value rest
  | _, [] => []
  end.

Definition LongestIncreasingSubsequence_cell
    (a : list Z)
    (i : nat)
    (dp : list Z)
    (j : nat) : list Z :=
  if Z.ltb
       (LongestIncreasingSubsequence_get a j)
       (LongestIncreasingSubsequence_get a i)
  then
    let newVal :=
      intMax
        (LongestIncreasingSubsequence_get dp i)
        (LongestIncreasingSubsequence_get dp j + 1) in
    LongestIncreasingSubsequence_set i newVal dp
  else dp.

Definition LongestIncreasingSubsequence_row
    (a : list Z)
    (dp : list Z)
    (i : nat) : list Z :=
  fold_left
    (LongestIncreasingSubsequence_cell a i)
    (seq 0%nat i)
    dp.

Definition LongestIncreasingSubsequence
    (a : list Z)
    (_h_precond : LongestIncreasingSubsequence_precond a) : Z :=
  let n := length a in
  let initial := repeat 1 n in
  let dp :=
    fold_left
      (LongestIncreasingSubsequence_row a)
      (seq 1%nat (Nat.pred n))
      initial in
  match dp with
  | [] => 0
  | _ => fold_left intMax dp 0
  end.

Definition LongestIncreasingSubsequence_allSubseq
    (a : list Z) : list (list Z) :=
  map
    (fun sub : list Z => rev sub)
    (fold_left
      (fun acc x =>
        acc ++ map (fun sub => x :: sub) acc)
      a [[]]).

Fixpoint LongestIncreasingSubsequence_pairwiseLess
    (xs : list Z) : bool :=
  match xs with
  | [] => true
  | x :: rest =>
      andb
        (forallb (fun y => Z.ltb x y) rest)
        (LongestIncreasingSubsequence_pairwiseLess rest)
  end.

Definition LongestIncreasingSubsequence_postcond
    (a : list Z)
    (result : Z)
    (_h_precond : LongestIncreasingSubsequence_precond a) : Prop :=
  let allSubseq :=
    LongestIncreasingSubsequence_allSubseq a in
  let increasingSubseqLens :=
    map
      (fun xs : list Z => Z.of_nat (length xs))
      (filter LongestIncreasingSubsequence_pairwiseLess allSubseq) in
  existsb (Z.eqb result) increasingSubseqLens = true /\
  forallb
    (fun candidate => Z.leb candidate result)
    increasingSubseqLens = true.

Theorem LongestIncreasingSubsequence_spec_satisfied
    (a : list Z)
    (h_precond : LongestIncreasingSubsequence_precond a) :
  LongestIncreasingSubsequence_postcond
    a
    (LongestIncreasingSubsequence a h_precond)
    h_precond.
Admitted.
