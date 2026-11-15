(* Statement-only formalization of VERINA corpus artifact verina_basic_52,
   catalog title "BubbleSort": executable bubble sort on an integer array,
   together with nondecreasing sortedness, permutation correctness, and the
   final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List
  Sorting.Permutation Sorting.Sorted ZArith.

Import ListNotations.

Definition BubbleSort_precond (_a : list Z) : Prop :=
  True.

Fixpoint bubbleSort_set_nth
    (index : nat)
    (value : Z)
    (a : list Z) : list Z :=
  match a with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: bubbleSort_set_nth index' value rest
      end
  end.

Definition swap
    (a : list Z)
    (i j : nat) : list Z :=
  let temp := nth i a 0%Z in
  let a1 := bubbleSort_set_nth i (nth j a 0%Z) a in
  bubbleSort_set_nth j temp a1.

Fixpoint bubbleInner_fuel
    (fuel j : nat)
    (a : list Z) : list Z :=
  match fuel with
  | O => a
  | S fuel' =>
      let a' :=
        if Z.gtb (nth j a 0%Z) (nth (S j) a 0%Z)
        then swap a j (S j)
        else a in
      bubbleInner_fuel fuel' (S j) a'
  end.

Definition bubbleInner
    (j i : nat)
    (a : list Z) : list Z :=
  bubbleInner_fuel (i - j)%nat j a.

Fixpoint bubbleOuter
    (i : nat)
    (a : list Z) : list Z :=
  match i with
  | O => a
  | S i' => bubbleOuter i' (bubbleInner 0%nat (S i') a)
  end.

Definition BubbleSort
    (a : list Z)
    (_h_precond : BubbleSort_precond a) : list Z :=
  if Nat.eqb (length a) 0%nat
  then a
  else bubbleOuter (length a - 1)%nat a.

Definition BubbleSort_postcond
    (a result : list Z)
    (_h_precond : BubbleSort_precond a) : Prop :=
  StronglySorted Z.le result /\
  Permutation result a.

Theorem BubbleSort_spec_satisfied
    (a : list Z)
    (h_precond : BubbleSort_precond a) :
  BubbleSort_postcond
    a (BubbleSort a h_precond) h_precond.
Admitted.
