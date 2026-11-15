(* Statement-only formalization of VERINA corpus artifact verina_advanced_38,
   catalog title "maxCoverageAfterRemovingOne": an executable computation of
   the greatest interval coverage obtainable by removing one interval,
   stably sorting by starting point, and merging overlaps, together with its
   maximizing-index correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition maxCoverageAfterRemovingOne_precond
    (intervals : list (nat * nat)) : Prop :=
  Nat.lt 0 (length intervals).

Fixpoint maxCoverageAfterRemovingOne_eraseIdx
    (intervals : list (nat * nat))
    (index : nat) : list (nat * nat) :=
  match index, intervals with
  | 0, [] => []
  | 0, _ :: rest => rest
  | S index', [] => []
  | S index', interval :: rest =>
      interval :: maxCoverageAfterRemovingOne_eraseIdx rest index'
  end.

Fixpoint maxCoverageAfterRemovingOne_merge_fuel
    (fuel : nat)
    (left right : list (nat * nat)) : list (nat * nat) :=
  match fuel with
  | 0 => left ++ right
  | S fuel' =>
      match left, right with
      | [], _ => right
      | _, [] => left
      | x :: xs, y :: ys =>
          if Nat.leb (fst x) (fst y)
          then
            x ::
              maxCoverageAfterRemovingOne_merge_fuel
                fuel' xs (y :: ys)
          else
            y ::
              maxCoverageAfterRemovingOne_merge_fuel
                fuel' (x :: xs) ys
      end
  end.

Definition maxCoverageAfterRemovingOne_merge
    (left right : list (nat * nat)) : list (nat * nat) :=
  maxCoverageAfterRemovingOne_merge_fuel
    (length left + length right) left right.

Fixpoint maxCoverageAfterRemovingOne_mergeSort_fuel
    (fuel : nat)
    (intervals : list (nat * nat)) : list (nat * nat) :=
  match fuel with
  | 0 => intervals
  | S fuel' =>
      match intervals with
      | [] => []
      | [interval] => [interval]
      | _ :: _ :: _ =>
          let splitPoint :=
            Nat.div (S (length intervals)) 2 in
          maxCoverageAfterRemovingOne_merge
            (maxCoverageAfterRemovingOne_mergeSort_fuel
              fuel' (firstn splitPoint intervals))
            (maxCoverageAfterRemovingOne_mergeSort_fuel
              fuel' (skipn splitPoint intervals))
      end
  end.

Definition maxCoverageAfterRemovingOne_mergeSort
    (intervals : list (nat * nat)) : list (nat * nat) :=
  maxCoverageAfterRemovingOne_mergeSort_fuel
    (length intervals) intervals.

Definition maxCoverageAfterRemovingOne_mergeStep
    (merged : list (nat * nat))
    (current : nat * nat) : list (nat * nat) :=
  match merged with
  | [] => [current]
  | (start, finish) :: rest =>
      if Nat.leb (fst current) finish
      then (start, Nat.max finish (snd current)) :: rest
      else current :: merged
  end.

Definition maxCoverageAfterRemovingOne_merged
    (intervals : list (nat * nat)) : list (nat * nat) :=
  fold_left
    maxCoverageAfterRemovingOne_mergeStep
    (maxCoverageAfterRemovingOne_mergeSort intervals)
    [].

Definition maxCoverageAfterRemovingOne_coverage
    (intervals : list (nat * nat)) : nat :=
  fold_left
    (fun total interval =>
      total + (snd interval - fst interval))
    (rev (maxCoverageAfterRemovingOne_merged intervals))
    0.

Definition maxCoverageAfterRemovingOne_coverageAfterRemoving
    (intervals : list (nat * nat))
    (index : nat) : nat :=
  maxCoverageAfterRemovingOne_coverage
    (maxCoverageAfterRemovingOne_eraseIdx intervals index).

Definition maxCoverageAfterRemovingOne
    (intervals : list (nat * nat))
    (_h_precond : maxCoverageAfterRemovingOne_precond intervals) : nat :=
  let n := length intervals in
  if Nat.leb n 1
  then 0
  else
    fold_left
      (fun best index =>
        Nat.max best
          (maxCoverageAfterRemovingOne_coverageAfterRemoving
            intervals index))
      (seq 0 n)
      0.

Definition maxCoverageAfterRemovingOne_postcond
    (intervals : list (nat * nat))
    (result : nat)
    (_h_precond : maxCoverageAfterRemovingOne_precond intervals) : Prop :=
  exists index : nat,
    Nat.lt index (length intervals) /\
    result =
      maxCoverageAfterRemovingOne_coverageAfterRemoving
        intervals index /\
    forall otherIndex : nat,
      Nat.lt otherIndex (length intervals) ->
      Nat.le
        (maxCoverageAfterRemovingOne_coverageAfterRemoving
          intervals otherIndex)
        (maxCoverageAfterRemovingOne_coverageAfterRemoving
          intervals index).

Theorem maxCoverageAfterRemovingOne_spec_satisfied
    (intervals : list (nat * nat))
    (h_precond : maxCoverageAfterRemovingOne_precond intervals) :
  maxCoverageAfterRemovingOne_postcond
    intervals
    (maxCoverageAfterRemovingOne intervals h_precond)
    h_precond.
Admitted.
