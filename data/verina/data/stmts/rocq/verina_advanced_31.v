(* Statement-only formalization of VERINA corpus artifact verina_advanced_31,
   catalog title "longestIncreasingSubseqLength": an executable exhaustive
   search computing the longest strictly increasing subsequence length of an
   integer list, together with its exhaustive-subsequence maximality contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition longestIncreasingSubseqLength_precond
    (_xs : list Z) : Prop :=
  True.

Fixpoint subsequences {A : Type}
    (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
      let subs := subsequences xs' in
      subs ++ map (fun s => x :: s) subs
  end.

Fixpoint isStrictlyIncreasing
    (xs : list Z) : bool :=
  match xs with
  | [] => true
  | _ :: [] => true
  | x :: (y :: rest as tail) =>
      if Z.ltb x y
      then isStrictlyIncreasing tail
      else false
  end.

Definition longestIncreasingSubseqLength
    (xs : list Z)
    (_h_precond : longestIncreasingSubseqLength_precond xs) : nat :=
  let subs := subsequences xs in
  let increasing := filter isStrictlyIncreasing subs in
  fold_left
    (fun acc s => Nat.max acc (length s))
    increasing 0%nat.

Definition longestIncreasingSubseqLength_allSubseq
    (xs : list Z) : list (list Z) :=
  map
    (fun sub : list Z => rev sub)
    (fold_left
      (fun acc x =>
        acc ++ map (fun sub => x :: sub) acc)
      xs [[]]).

Fixpoint longestIncreasingSubseqLength_pairwiseLess
    (xs : list Z) : bool :=
  match xs with
  | [] => true
  | x :: rest =>
      andb
        (forallb (fun y => Z.ltb x y) rest)
        (longestIncreasingSubseqLength_pairwiseLess rest)
  end.

Definition longestIncreasingSubseqLength_postcond
    (xs : list Z)
    (result : nat)
    (_h_precond : longestIncreasingSubseqLength_precond xs) : Prop :=
  let allSubseq :=
    longestIncreasingSubseqLength_allSubseq xs in
  let increasingSubseqLens :=
    map
      (fun sub : list Z => length sub)
      (filter
        longestIncreasingSubseqLength_pairwiseLess
        allSubseq) in
  existsb (Nat.eqb result) increasingSubseqLens = true /\
  forallb
    (fun candidate => Nat.leb candidate result)
    increasingSubseqLens = true.

Theorem longestIncreasingSubseqLength_spec_satisfied
    (xs : list Z)
    (h_precond : longestIncreasingSubseqLength_precond xs) :
  longestIncreasingSubseqLength_postcond
    xs
    (longestIncreasingSubseqLength xs h_precond)
    h_precond.
Admitted.
