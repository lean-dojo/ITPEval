(* Statement-only formalization of VERINA corpus artifact verina_advanced_16,
   catalog title "insertionSort": executable insertion sort on integer lists,
   with sortedness and permutation correctness. This file contains no proof. *)

From Stdlib Require Import Lists.List Sorting.Permutation Sorting.Sorted ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition insertionSort_precond (_xs : list Z) : Prop :=
  True.

Fixpoint insertionSort_insert
    (x : Z) (ys : list Z) : list Z :=
  match ys with
  | [] => [x]
  | y :: ys' =>
      if Z.leb x y
      then x :: y :: ys'
      else y :: insertionSort_insert x ys'
  end.

Fixpoint insertionSort_sort (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: xs' =>
      insertionSort_insert x (insertionSort_sort xs')
  end.

Definition insertionSort
    (xs : list Z)
    (_h_precond : insertionSort_precond xs) : list Z :=
  insertionSort_sort xs.

Definition insertionSort_postcond
    (xs result : list Z)
    (_h_precond : insertionSort_precond xs) : Prop :=
  StronglySorted Z.le result /\
  Permutation xs result.

Theorem insertionSort_spec_satisfied
    (xs : list Z)
    (h_precond : insertionSort_precond xs) :
  insertionSort_postcond
    xs (insertionSort xs h_precond) h_precond.
Admitted.
