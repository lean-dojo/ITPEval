(* Statement-only formalization of VERINA corpus artifact verina_basic_24,
   catalog title "firstEvenOddDifference": an executable left-to-right scan
   of an integer array returns its first even value minus its first odd value,
   together with the parity-existence precondition, first-index postcondition,
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition isEven (n : Z) : bool :=
  Z.eqb (Z.modulo n 2) 0.

Definition isOdd (n : Z) : bool :=
  negb (Z.eqb (Z.modulo n 2) 0).

Definition firstEvenOddDifference_precond
    (a : list Z) : Prop :=
  (1 < length a)%nat /\
  (exists x : Z, In x a /\ isEven x = true) /\
  (exists x : Z, In x a /\ isOdd x = true).

Definition firstEvenOddDifference_record_first
    (current : option nat)
    (i : nat)
    (matches : bool) : option nat :=
  match current with
  | Some j => Some j
  | None => if matches then Some i else None
  end.

Fixpoint firstEvenOddDifference_findFirstEvenOdd
    (a remaining : list Z)
    (i : nat)
    (firstEven firstOdd : option nat) : Z :=
  match remaining with
  | [] => 0%Z
  | x :: xs =>
      let newFirstEven :=
        firstEvenOddDifference_record_first firstEven i (isEven x) in
      let newFirstOdd :=
        firstEvenOddDifference_record_first firstOdd i (isOdd x) in
      match newFirstEven, newFirstOdd with
      | Some e, Some o => nth e a 0%Z - nth o a 0%Z
      | _, _ =>
          firstEvenOddDifference_findFirstEvenOdd
            a xs (S i) newFirstEven newFirstOdd
      end
  end.

Definition firstEvenOddDifference
    (a : list Z)
    (_h_precond : firstEvenOddDifference_precond a) : Z :=
  firstEvenOddDifference_findFirstEvenOdd a a 0%nat None None.

Definition firstEvenOddDifference_postcond
    (a : list Z)
    (result : Z)
    (_h_precond : firstEvenOddDifference_precond a) : Prop :=
  exists i j : nat,
    (i < length a)%nat /\
    (j < length a)%nat /\
    isEven (nth i a 0%Z) = true /\
    isOdd (nth j a 0%Z) = true /\
    result = nth i a 0%Z - nth j a 0%Z /\
    (forall k : nat,
      (k < i)%nat -> isOdd (nth k a 0%Z) = true) /\
    (forall k : nat,
      (k < j)%nat -> isEven (nth k a 0%Z) = true).

Theorem firstEvenOddDifference_spec_satisfied
    (a : list Z)
    (h_precond : firstEvenOddDifference_precond a) :
  firstEvenOddDifference_postcond
    a (firstEvenOddDifference a h_precond) h_precond.
Admitted.
