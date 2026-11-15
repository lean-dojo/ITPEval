(* Statement-only formalization of VERINA corpus artifact verina_basic_77,
   catalog title "modify_array_element": executable replacement of one
   bounded element in a two-dimensional natural-number array, together with
   its bounds precondition, unchanged-other-elements postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Definition modify_array_element_precond
    (arr : list (list nat))
    (index1 index2 val : nat) : Prop :=
  (index1 < length arr)%nat /\
  (index2 < length (nth index1 arr []))%nat.

Fixpoint modify_array_element_set_nth {A : Type}
    (index : nat)
    (value : A)
    (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' =>
          x :: modify_array_element_set_nth index' value rest
      end
  end.

Definition updateInner
    (a : list nat)
    (idx val : nat) : list nat :=
  modify_array_element_set_nth idx val a.

Definition modify_array_element
    (arr : list (list nat))
    (index1 index2 val : nat)
    (_h_precond :
      modify_array_element_precond arr index1 index2 val)
    : list (list nat) :=
  let inner := nth index1 arr [] in
  let inner' := updateInner inner index2 val in
  modify_array_element_set_nth index1 inner' arr.

Definition modify_array_element_postcond
    (arr : list (list nat))
    (index1 index2 val : nat)
    (result : list (list nat))
    (_h_precond :
      modify_array_element_precond arr index1 index2 val)
    : Prop :=
  length result = length arr /\
  length (nth index1 result []) =
    length (nth index1 arr []) /\
  (forall i : nat,
      (i < length arr)%nat ->
      i <> index1 ->
      nth i result [] = nth i arr []) /\
  (forall j : nat,
      (j < length (nth index1 arr []))%nat ->
      j <> index2 ->
      nth j (nth index1 result []) 0%nat =
        nth j (nth index1 arr []) 0%nat) /\
  nth index2 (nth index1 result []) 0%nat = val.

Theorem modify_array_element_spec_satisfied
    (arr : list (list nat))
    (index1 index2 val : nat)
    (h_precond :
      modify_array_element_precond arr index1 index2 val) :
  modify_array_element_postcond
    arr index1 index2 val
    (modify_array_element arr index1 index2 val h_precond)
    h_precond.
Admitted.
