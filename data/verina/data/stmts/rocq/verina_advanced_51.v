(* Statement-only formalization of VERINA corpus artifact verina_advanced_51,
   catalog title "mergeSorted": an executable stable merge of two
   nondecreasing integer lists, together with nondecreasing sortedness and
   permutation-of-concatenation correctness. This file contains no proof. *)

From Stdlib Require Import Lists.List Sorting.Permutation Sorting.Sorted ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition mergeSorted_precond
    (a b : list Z) : Prop :=
  StronglySorted Z.le a /\
  StronglySorted Z.le b.

Fixpoint mergeSortedAux_fuel
    (fuel : nat)
    (a b : list Z) : list Z :=
  match fuel with
  | O => a ++ b
  | S fuel' =>
      match a, b with
      | [], _ => b
      | _, [] => a
      | x :: xs, y :: ys =>
          if Z.leb x y
          then x :: mergeSortedAux_fuel fuel' xs (y :: ys)
          else y :: mergeSortedAux_fuel fuel' (x :: xs) ys
      end
  end.

Definition mergeSortedAux
    (a b : list Z) : list Z :=
  mergeSortedAux_fuel (Nat.add (length a) (length b)) a b.

Definition mergeSorted
    (a b : list Z)
    (_h_precond : mergeSorted_precond a b) : list Z :=
  let merged := mergeSortedAux a b in
  merged.

Definition mergeSorted_postcond
    (a b result : list Z)
    (_h_precond : mergeSorted_precond a b) : Prop :=
  StronglySorted Z.le result /\
  Permutation result (a ++ b).

Theorem mergeSorted_spec_satisfied
    (a b : list Z)
    (h_precond : mergeSorted_precond a b) :
  mergeSorted_postcond
    a b
    (mergeSorted a b h_precond)
    h_precond.
Admitted.
