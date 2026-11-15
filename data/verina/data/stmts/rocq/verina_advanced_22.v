(* Statement-only formalization of VERINA corpus artifact verina_advanced_22,
   catalog title "isPeakValley": an executable Boolean scan deciding whether
   an integer list strictly increases and then strictly decreases, together
   with its finite-index correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition isPeakValley_precond (_lst : list Z) : Prop :=
  True.

Fixpoint isPeakValley_aux_from
    (previous : Z)
    (remaining : list Z)
    (increasing startedDecreasing : bool) : bool :=
  match remaining with
  | [] => andb increasing startedDecreasing
  | y :: rest =>
      if Z.ltb previous y
      then
        if startedDecreasing
        then false
        else isPeakValley_aux_from y rest true startedDecreasing
      else
        if Z.ltb y previous
        then
          if increasing
          then isPeakValley_aux_from y rest increasing true
          else false
        else false
  end.

Definition isPeakValley_aux
    (l : list Z)
    (increasing startedDecreasing : bool) : bool :=
  match l with
  | [] => andb increasing startedDecreasing
  | x :: rest =>
      isPeakValley_aux_from x rest increasing startedDecreasing
  end.

Definition isPeakValley
    (lst : list Z)
    (_h_precond : isPeakValley_precond lst) : bool :=
  isPeakValley_aux lst false false.

Definition isPeakValley_isValidPeak
    (lst : list Z) (len p : nat) : bool :=
  andb
    (Nat.leb 1 p)
    (andb
      (Nat.ltb p (len - 1))
      (andb
        (forallb
          (fun i =>
            Z.ltb
              (nth i lst 0%Z)
              (nth (i + 1) lst 0%Z))
          (seq 0 p))
        (forallb
          (fun i =>
            Z.ltb
              (nth (p + i + 1) lst 0%Z)
              (nth (p + i) lst 0%Z))
          (seq 0 (len - 1 - p))))).

Definition isPeakValley_validPeaks
    (lst : list Z) : list nat :=
  let len := length lst in
  filter
    (isPeakValley_isValidPeak lst len)
    (seq 0 len).

Definition isPeakValley_postcond
    (lst : list Z)
    (result : bool)
    (_h_precond : isPeakValley_precond lst) : Prop :=
  let validPeaks := isPeakValley_validPeaks lst in
  (validPeaks <> [] -> result = true) /\
  (length validPeaks = 0%nat -> result <> true).

Theorem isPeakValley_spec_satisfied
    (lst : list Z)
    (h_precond : isPeakValley_precond lst) :
  isPeakValley_postcond
    lst (isPeakValley lst h_precond) h_precond.
Admitted.
