(* Statement-only formalization of VERINA corpus artifact verina_advanced_17,
   catalog title "insertionSort": executable insertion sort on integer lists,
   with nondecreasing sortedness and permutation correctness. This file
   contains no proof. *)

From Stdlib Require Import Lists.List Sorting.Permutation Sorting.Sorted ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition insertionSort_precond (_l : list Z) : Prop :=
  True.

Fixpoint insertElement (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | y :: ys =>
      if Z.leb x y
      then x :: y :: ys
      else y :: insertElement x ys
  end.

Fixpoint sortList (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => insertElement x (sortList xs)
  end.

Definition insertionSort
    (l : list Z)
    (_h_precond : insertionSort_precond l) : list Z :=
  let result := sortList l in
  result.

Definition insertionSort_postcond
    (l result : list Z)
    (_h_precond : insertionSort_precond l) : Prop :=
  StronglySorted Z.le result /\
  Permutation l result.

Theorem insertionSort_spec_satisfied
    (l : list Z)
    (h_precond : insertionSort_precond l) :
  insertionSort_postcond
    l (insertionSort l h_precond) h_precond.
Admitted.
