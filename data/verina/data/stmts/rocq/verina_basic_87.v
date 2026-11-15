(* Statement-only formalization of VERINA corpus artifact verina_basic_87,
   catalog title "SelectionSort": executable selection sort on an arbitrary
   integer array, together with its unconditional precondition,
   nondecreasing sortedness and permutation postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List
  Sorting.Permutation Sorting.Sorted ZArith.

Import ListNotations.

Module VerinaBasic87.

Definition SelectionSort_precond (_a : list Z) : Prop :=
  True.

Definition findMinIndexInRange
    (arr : list Z)
    (start finish : nat) : nat :=
  fold_left
    (fun minIdx i =>
      let currIdx := (start + i)%nat in
      if Z.ltb (nth currIdx arr 0%Z) (nth minIdx arr 0%Z)
      then currIdx
      else minIdx)
    (seq 0%nat (finish - start)%nat)
    start.

Fixpoint selectionSort_set_nth
    (index : nat)
    (value : Z)
    (a : list Z) : list Z :=
  match a with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: selectionSort_set_nth index' value rest
      end
  end.

Definition swap
    (a : list Z)
    (i j : nat) : list Z :=
  if andb
      (andb
        (Nat.ltb i (length a))
        (Nat.ltb j (length a)))
      (negb (Nat.eqb i j))
  then
    let temp := nth i a 0%Z in
    let a' := selectionSort_set_nth i (nth j a 0%Z) a in
    selectionSort_set_nth j temp a'
  else a.

Definition SelectionSort
    (a : list Z)
    (_h_precond : SelectionSort_precond a) : list Z :=
  fold_left
    (fun arr i =>
      let minIdx :=
        findMinIndexInRange arr i (length a) in
      swap arr i minIdx)
    (seq 0%nat (length a))
    a.

Definition SelectionSort_postcond
    (a result : list Z)
    (_h_precond : SelectionSort_precond a) : Prop :=
  StronglySorted Z.le result /\
  Permutation a result.

Theorem SelectionSort_spec_satisfied
    (a : list Z)
    (h_precond : SelectionSort_precond a) :
  SelectionSort_postcond
    a (SelectionSort a h_precond) h_precond.
Admitted.

End VerinaBasic87.
