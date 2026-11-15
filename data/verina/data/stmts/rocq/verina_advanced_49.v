(* Statement-only formalization of VERINA corpus artifact verina_advanced_49,
   catalog title "mergeSortedLists": an executable stable merge of two
   nondecreasing integer lists, together with nondecreasing sortedness and
   permutation correctness. This file contains no proof. *)

From Stdlib Require Import Lists.List Sorting.Permutation Sorting.Sorted ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition mergeSortedLists_precond
    (arr1 arr2 : list Z) : Prop :=
  StronglySorted Z.le arr1 /\
  StronglySorted Z.le arr2.

Fixpoint mergeSortedLists_merge_fuel
    (fuel : nat)
    (xs ys : list Z) : list Z :=
  match fuel with
  | O => xs ++ ys
  | S fuel' =>
      match xs, ys with
      | [], _ => ys
      | _, [] => xs
      | x :: xt, y :: yt =>
          if Z.leb x y
          then
            x ::
              mergeSortedLists_merge_fuel
                fuel' xt (y :: yt)
          else
            y ::
              mergeSortedLists_merge_fuel
                fuel' (x :: xt) yt
      end
  end.

Definition mergeSortedLists_merge
    (xs ys : list Z) : list Z :=
  mergeSortedLists_merge_fuel
    (Nat.add (length xs) (length ys)) xs ys.

Definition mergeSortedLists
    (arr1 arr2 : list Z)
    (_h_precond : mergeSortedLists_precond arr1 arr2) :
    list Z :=
  mergeSortedLists_merge arr1 arr2.

Definition mergeSortedLists_postcond
    (arr1 arr2 result : list Z)
    (_h_precond : mergeSortedLists_precond arr1 arr2) : Prop :=
  StronglySorted Z.le result /\
  Permutation (arr1 ++ arr2) result.

Theorem mergeSortedLists_spec_satisfied
    (arr1 arr2 : list Z)
    (h_precond : mergeSortedLists_precond arr1 arr2) :
  mergeSortedLists_postcond
    arr1 arr2
    (mergeSortedLists arr1 arr2 h_precond)
    h_precond.
Admitted.
