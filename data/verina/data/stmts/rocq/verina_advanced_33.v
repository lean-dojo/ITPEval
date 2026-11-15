(* Statement-only formalization of VERINA corpus artifact verina_advanced_33,
   catalog title "longestIncreasingSubsequence": an executable recursive
   include-or-skip computation of the longest strictly increasing subsequence
   length of an integer list, together with its exhaustive-subsequence
   maximality contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition longestIncreasingSubsequence_precond
    (_nums : list Z) : Prop :=
  True.

Definition longestIncreasingSubsequence_max2
    (a b : nat) : nat :=
  if Nat.ltb b a then a else b.

Fixpoint longestIncreasingSubsequence_listLength
    (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | _ :: xs => S (longestIncreasingSubsequence_listLength xs)
  end.

Fixpoint longestIncreasingSubsequence_helper
    (lst : list Z)
    (prev : option Z) : nat :=
  match lst with
  | [] => 0%nat
  | h :: t =>
      let canTake :=
        match prev with
        | None => true
        | Some p => Z.ltb p h
        end in
      let withTake :=
        if canTake
        then S (longestIncreasingSubsequence_helper t (Some h))
        else 0%nat in
      let withoutTake :=
        longestIncreasingSubsequence_helper t prev in
      longestIncreasingSubsequence_max2 withTake withoutTake
  end.

Definition longestIncreasingSubsequence
    (nums : list Z)
    (_h_precond : longestIncreasingSubsequence_precond nums) : nat :=
  longestIncreasingSubsequence_helper nums None.

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
    (result : nat)
    (_h_precond : longestIncreasingSubsequence_precond nums) : Prop :=
  let allSubseq :=
    longestIncreasingSubsequence_allSubseq nums in
  let increasingSubseqLens :=
    map
      (fun xs : list Z => length xs)
      (filter longestIncreasingSubsequence_pairwiseLess allSubseq) in
  existsb (Nat.eqb result) increasingSubseqLens = true /\
  forallb
    (fun candidate => Nat.leb candidate result)
    increasingSubseqLens = true.

Theorem longestIncreasingSubsequence_spec_satisfied
    (nums : list Z)
    (h_precond : longestIncreasingSubsequence_precond nums) :
  longestIncreasingSubsequence_postcond
    nums
    (longestIncreasingSubsequence nums h_precond)
    h_precond.
Admitted.
