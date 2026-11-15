(* Statement-only formalization of VERINA corpus artifact verina_advanced_40,
   catalog title "maxOfList": an executable recursive computation of the
   maximum element of a nonempty natural-number list, together with its
   membership and upper-bound correctness contract. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Definition maxOfList_precond (lst : list nat) : Prop :=
  lst <> [].

Fixpoint maxOfList_helper (lst : list nat) : nat :=
  match lst with
  | [] => 0
  | [x] => x
  | x :: xs =>
      let maxTail := maxOfList_helper xs in
      if Nat.ltb maxTail x then x else maxTail
  end.

Definition maxOfList
    (lst : list nat)
    (_h_precond : maxOfList_precond lst) : nat :=
  maxOfList_helper lst.

Definition maxOfList_postcond
    (lst : list nat)
    (result : nat)
    (_h_precond : maxOfList_precond lst) : Prop :=
  In result lst /\
  forall x : nat, In x lst -> Nat.le x result.

Theorem maxOfList_spec_satisfied
    (lst : list nat)
    (h_precond : maxOfList_precond lst) :
  maxOfList_postcond
    lst (maxOfList lst h_precond) h_precond.
Admitted.
