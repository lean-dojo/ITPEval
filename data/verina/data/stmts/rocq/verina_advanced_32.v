(* Statement-only formalization of VERINA corpus artifact verina_advanced_32,
   catalog title "longestIncreasingSubsequence": an executable table-building
   computation of the longest strictly increasing subsequence length of an
   integer list, together with its exhaustive-subsequence maximality contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition longestIncreasingSubsequence_precond
    (_numbers : list Z) : Prop :=
  True.

Fixpoint longestIncreasingSubsequence_findMaxLength
    (lengths : list nat) : nat :=
  match lengths with
  | [] => 0%nat
  | x :: xs =>
      let maxRest :=
        longestIncreasingSubsequence_findMaxLength xs in
      if Nat.ltb maxRest x then x else maxRest
  end.

Fixpoint longestIncreasingSubsequence_findLengthEndingAtCurr
    (currNum : Z)
    (prevNums : list Z)
    (lengths : list nat)
    (best : nat) : nat :=
  match prevNums, lengths with
  | prevVal :: restVals, prevLen :: restLens =>
      if Z.ltb prevVal currNum
      then
        longestIncreasingSubsequence_findLengthEndingAtCurr
          currNum restVals restLens (Nat.max best prevLen)
      else
        longestIncreasingSubsequence_findLengthEndingAtCurr
          currNum restVals restLens best
  | _, _ => best
  end.

Fixpoint longestIncreasingSubsequence_buildTables
    (remaining : list Z)
    (prevNums : list Z)
    (lengths : list nat)
    (idx : nat) : nat :=
  match remaining with
  | [] =>
      longestIncreasingSubsequence_findMaxLength lengths
  | currNum :: restNums =>
      let bestPrevLen :=
        longestIncreasingSubsequence_findLengthEndingAtCurr
          currNum prevNums lengths 0%nat in
      let currLength := S bestPrevLen in
      longestIncreasingSubsequence_buildTables
        restNums
        (prevNums ++ [currNum])
        (lengths ++ [currLength])
        (S idx)
  end.

Definition longestIncreasingSubsequence
    (numbers : list Z)
    (_h_precond : longestIncreasingSubsequence_precond numbers) : nat :=
  match numbers with
  | [] => 0%nat
  | [_] => 1%nat
  | first :: rest =>
      longestIncreasingSubsequence_buildTables
        rest [first] [1%nat] 1%nat
  end.

Definition longestIncreasingSubsequence_allSubseq
    (numbers : list Z) : list (list Z) :=
  map
    (fun sub : list Z => rev sub)
    (fold_left
      (fun acc x =>
        acc ++ map (fun sub => x :: sub) acc)
      numbers [[]]).

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
    (numbers : list Z)
    (result : nat)
    (_h_precond : longestIncreasingSubsequence_precond numbers) : Prop :=
  let allSubseq :=
    longestIncreasingSubsequence_allSubseq numbers in
  let increasingSubseqLens :=
    map
      (fun xs : list Z => length xs)
      (filter longestIncreasingSubsequence_pairwiseLess allSubseq) in
  existsb (Nat.eqb result) increasingSubseqLens = true /\
  forallb
    (fun candidate => Nat.leb candidate result)
    increasingSubseqLens = true.

Theorem longestIncreasingSubsequence_spec_satisfied
    (numbers : list Z)
    (h_precond : longestIncreasingSubsequence_precond numbers) :
  longestIncreasingSubsequence_postcond
    numbers
    (longestIncreasingSubsequence numbers h_precond)
    h_precond.
Admitted.
