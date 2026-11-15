(* Statement-only formalization of VERINA corpus artifact verina_basic_57,
   catalog title "CountLessThan": executable counting of the integers in an
   array that are strictly below a threshold, together with its
   no-precondition correctness contract. This file contains no proof. *)

From Stdlib Require Import Lists.List ZArith.

Fixpoint countLessThan_count
    (fuel i acc : nat)
    (numbers : list Z)
    (threshold : Z) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.ltb i (length numbers)
      then
        let new_acc :=
          if Z.ltb (nth i numbers 0%Z) threshold
          then S acc
          else acc in
        countLessThan_count fuel' (S i) new_acc numbers threshold
      else acc
  end.

Definition countLessThan
    (numbers : list Z)
    (threshold : Z) : nat :=
  countLessThan_count
    (length numbers) 0%nat 0%nat numbers threshold.

Definition CountLessThan_precond
    (_numbers : list Z)
    (_threshold : Z) : Prop :=
  True.

Definition CountLessThan
    (numbers : list Z)
    (threshold : Z)
    (_h_precond : CountLessThan_precond numbers threshold) : nat :=
  countLessThan numbers threshold.

Definition CountLessThan_expected
    (numbers : list Z)
    (threshold : Z) : nat :=
  fold_left
    (fun count n =>
      if Z.ltb n threshold then S count else count)
    numbers 0%nat.

Definition CountLessThan_postcond
    (numbers : list Z)
    (threshold : Z)
    (result : nat)
    (_h_precond : CountLessThan_precond numbers threshold) : Prop :=
  Nat.sub result (CountLessThan_expected numbers threshold) = 0%nat /\
  Nat.sub (CountLessThan_expected numbers threshold) result = 0%nat.

Theorem CountLessThan_spec_satisfied
    (numbers : list Z)
    (threshold : Z)
    (h_precond : CountLessThan_precond numbers threshold) :
  CountLessThan_postcond
    numbers threshold
    (CountLessThan numbers threshold h_precond)
    h_precond.
Admitted.
