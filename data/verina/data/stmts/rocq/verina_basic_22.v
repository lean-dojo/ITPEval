(* Statement-only formalization of VERINA corpus artifact verina_basic_22,
   catalog title "dissimilarElements": an executable integer-array program
   computes the sorted duplicate-free symmetric difference of two arrays,
   together with its unconditional precondition, full postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Fixpoint inArray (a : list Z) (x : Z) : bool :=
  match a with
  | [] => false
  | y :: ys =>
      if Z.eqb y x then true else inArray ys x
  end.

Definition dissimilarElements_precond
    (_a _b : list Z) : Prop :=
  True.

Definition dissimilarElements_set_insert
    (acc : list Z) (x : Z) : list Z :=
  if inArray acc x then acc else x :: acc.

Definition dissimilarElements_collect
    (other acc : list Z) (x : Z) : list Z :=
  if negb (inArray other x)
  then dissimilarElements_set_insert acc x
  else acc.

Fixpoint dissimilarElements_sorted_insert
    (x : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [x]
  | y :: ys =>
      if Z.leb x y
      then x :: y :: ys
      else y :: dissimilarElements_sorted_insert x ys
  end.

Fixpoint dissimilarElements_sort
    (values : list Z) : list Z :=
  match values with
  | [] => []
  | x :: xs =>
      dissimilarElements_sorted_insert
        x (dissimilarElements_sort xs)
  end.

Definition dissimilarElements
    (a b : list Z)
    (_h_precond : dissimilarElements_precond a b) : list Z :=
  let from_a :=
    fold_left (dissimilarElements_collect b) a [] in
  let from_both :=
    fold_left (dissimilarElements_collect a) b from_a in
  dissimilarElements_sort from_both.

Fixpoint dissimilarElements_pairwise_le
    (values : list Z) : Prop :=
  match values with
  | [] => True
  | x :: xs =>
      Forall (fun y => (x <= y)%Z) xs /\
      dissimilarElements_pairwise_le xs
  end.

Definition dissimilarElements_postcond
    (a b result : list Z)
    (_h_precond : dissimilarElements_precond a b) : Prop :=
  Forall (fun x => inArray a x <> inArray b x) result /\
  dissimilarElements_pairwise_le result /\
  NoDup result /\
  Forall
    (fun x =>
      if inArray b x
      then ~ In x result
      else In x result)
    a /\
  Forall
    (fun x =>
      if inArray a x
      then ~ In x result
      else In x result)
    b.

Theorem dissimilarElements_spec_satisfied
    (a b : list Z)
    (h_precond : dissimilarElements_precond a b) :
  dissimilarElements_postcond
    a b (dissimilarElements a b h_precond) h_precond.
Admitted.
