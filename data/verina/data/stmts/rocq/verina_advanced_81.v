(* Statement-only formalization of VERINA corpus artifact verina_advanced_81,
   catalog title "uniqueSorted": executable first-occurrence deduplication
   followed by insertion sorting of an integer list, together with its
   precondition, permutation-and-pairwise-order postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List Sorting.Permutation ZArith.

Import ListNotations.

Definition uniqueSorted_precond (_arr : list Z) : Prop :=
  True.

Fixpoint uniqueSorted_insert
    (x : Z)
    (sorted : list Z) : list Z :=
  match sorted with
  | [] => [x]
  | head :: tail =>
      if Z.leb x head
      then x :: head :: tail
      else head :: uniqueSorted_insert x tail
  end.

Fixpoint uniqueSorted_insertionSort
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | head :: tail =>
      uniqueSorted_insert
        head
        (uniqueSorted_insertionSort tail)
  end.

Fixpoint uniqueSorted_removeDups_aux
    (remaining seen acc : list Z) : list Z :=
  match remaining with
  | [] => rev acc
  | head :: tail =>
      if existsb (Z.eqb head) seen
      then uniqueSorted_removeDups_aux tail seen acc
      else uniqueSorted_removeDups_aux
             tail (head :: seen) (head :: acc)
  end.

Definition uniqueSorted_removeDups
    (xs : list Z) : list Z :=
  uniqueSorted_removeDups_aux xs [] [].

Definition uniqueSorted
    (arr : list Z)
    (_h_precond : uniqueSorted_precond arr) : list Z :=
  uniqueSorted_insertionSort (uniqueSorted_removeDups arr).

Inductive uniqueSorted_pairwise
    {A : Type}
    (relation : A -> A -> Prop) : list A -> Prop :=
| uniqueSorted_pairwise_nil :
    uniqueSorted_pairwise relation []
| uniqueSorted_pairwise_cons :
    forall (head : A) (tail : list A),
      Forall (relation head) tail ->
      uniqueSorted_pairwise relation tail ->
      uniqueSorted_pairwise relation (head :: tail).

Definition uniqueSorted_postcond
    (arr result : list Z)
    (_h_precond : uniqueSorted_precond arr) : Prop :=
  Permutation (uniqueSorted_removeDups arr) result /\
  uniqueSorted_pairwise Z.le result.

Theorem uniqueSorted_spec_satisfied
    (arr : list Z)
    (h_precond : uniqueSorted_precond arr) :
  uniqueSorted_postcond
    arr (uniqueSorted arr h_precond) h_precond.
Admitted.
