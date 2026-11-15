(* Statement-only formalization of VERINA corpus artifact verina_advanced_34,
   catalog title "longestIncreasingSubsequence": an executable patience-sorting
   computation using lower-bound binary search for the longest strictly
   increasing subsequence length of an integer list, together with its
   exhaustive-subsequence maximality contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition longestIncreasingSubsequence_precond
    (_nums : list Z) : Prop :=
  True.

Fixpoint longestIncreasingSubsequence_set_nth
    (index : nat) (value : Z) (xs : list Z) : list Z :=
  match index, xs with
  | 0%nat, _ :: rest => value :: rest
  | S index', x :: rest =>
      x :: longestIncreasingSubsequence_set_nth index' value rest
  | _, [] => []
  end.

Fixpoint binarySearchLeft_fuel
    (fuel : nat)
    (sub : list Z)
    (num : Z)
    (left right : nat) : nat :=
  match fuel with
  | 0%nat => left
  | S fuel' =>
      if Nat.ltb left right then
        let mid := Nat.div (Nat.add left right) 2%nat in
        let midValue := nth mid sub 0%Z in
        if Z.eqb midValue num then
          binarySearchLeft_fuel fuel' sub num left mid
        else if Z.ltb midValue num then
          binarySearchLeft_fuel fuel' sub num (S mid) right
        else
          binarySearchLeft_fuel fuel' sub num left mid
      else
        left
  end.

Definition binarySearchLeft
    (sub : list Z)
    (num : Z)
    (left right : nat) : nat :=
  binarySearchLeft_fuel
    (S (Nat.sub right left)) sub num left right.

Definition longestIncreasingSubsequence_step
    (sub : list Z) (num : Z) : list Z :=
  if Z.ltb (last sub 0%Z) num then
    sub ++ [num]
  else
    let left :=
      binarySearchLeft sub num 0%nat (Nat.pred (length sub)) in
    longestIncreasingSubsequence_set_nth left num sub.

Definition longestIncreasingSubsequence
    (nums : list Z)
    (_h_precond : longestIncreasingSubsequence_precond nums) : Z :=
  match nums with
  | [] => 0%Z
  | first :: rest =>
      Z.of_nat
        (length
          (fold_left
            longestIncreasingSubsequence_step rest [first]))
  end.

Definition longestIncreasingSubsequence_allSubseq
    (nums : list Z) : list (list Z) :=
  map
    (fun sub : list Z => rev sub)
    (fold_left
      (fun acc x =>
        acc ++ map (fun sub => x :: sub) acc)
      nums [[]]).

Fixpoint longestIncreasingSubsequence_pairwiseLess
    (xs : list Z) : bool :=
  match xs with
  | [] => true
  | x :: rest =>
      andb
        (forallb (fun y => Z.ltb x y) rest)
        (longestIncreasingSubsequence_pairwiseLess rest)
  end.

Definition longestIncreasingSubsequence_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : longestIncreasingSubsequence_precond nums) : Prop :=
  let allSubseq :=
    longestIncreasingSubsequence_allSubseq nums in
  let increasingSubseqLens :=
    map
      (fun xs : list Z => Z.of_nat (length xs))
      (filter longestIncreasingSubsequence_pairwiseLess allSubseq) in
  existsb (Z.eqb result) increasingSubseqLens = true /\
  forallb
    (fun candidate => Z.leb candidate result)
    increasingSubseqLens = true.

Theorem longestIncreasingSubsequence_spec_satisfied
    (nums : list Z)
    (h_precond : longestIncreasingSubsequence_precond nums) :
  longestIncreasingSubsequence_postcond
    nums
    (longestIncreasingSubsequence nums h_precond)
    h_precond.
Admitted.
