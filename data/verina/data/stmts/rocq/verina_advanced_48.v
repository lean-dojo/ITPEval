(* Statement-only formalization of VERINA corpus artifact verina_advanced_48,
   catalog title "mergeSort": an executable insertion-sort computation on
   integer lists, exposed as mergeSort, together with nondecreasing sortedness
   and permutation correctness. This file contains no proof. *)

From Stdlib Require Import Lists.List Sorting.Permutation Sorting.Sorted ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition mergeSort_precond (_list : list Z) : Prop :=
  True.

Fixpoint mergeSort_insert
    (x : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [x]
  | y :: ys =>
      if Z.leb x y
      then x :: y :: ys
      else y :: mergeSort_insert x ys
  end.

Fixpoint mergeSort_sort (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: xs =>
      let sortedRest := mergeSort_sort xs in
      mergeSort_insert x sortedRest
  end.

Definition mergeSort
    (xs : list Z)
    (_h_precond : mergeSort_precond xs) : list Z :=
  mergeSort_sort xs.

Definition mergeSort_postcond
    (xs result : list Z)
    (_h_precond : mergeSort_precond xs) : Prop :=
  StronglySorted Z.le result /\
  Permutation xs result.

Theorem mergeSort_spec_satisfied
    (xs : list Z)
    (h_precond : mergeSort_precond xs) :
  mergeSort_postcond
    xs (mergeSort xs h_precond) h_precond.
Admitted.
