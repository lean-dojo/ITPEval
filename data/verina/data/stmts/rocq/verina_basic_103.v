(* Statement-only formalization of VERINA corpus artifact verina_basic_103,
   catalog title "UpdateElements": an executable update of an integer array
   that increments index 4 by 3 and sets index 7 to 516, together with its
   precondition, postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition UpdateElements_precond (a : list Z) : Prop :=
  (8 <= length a)%nat.

Fixpoint UpdateElements_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | 0%nat => value :: rest
      | S index' =>
          x :: UpdateElements_set_nth index' value rest
      end
  end.

Definition UpdateElements
    (a : list Z)
    (_h_precond : UpdateElements_precond a) : list Z :=
  let a1 :=
    UpdateElements_set_nth
      4%nat (nth 4%nat a 0%Z + 3) a in
  let a2 :=
    UpdateElements_set_nth 7%nat 516 a1 in
  a2.

Definition UpdateElements_postcond
    (a result : list Z)
    (_h_precond : UpdateElements_precond a) : Prop :=
  length result = length a /\
  nth 4%nat result 0%Z = nth 4%nat a 0%Z + 3 /\
  nth 7%nat result 0%Z = 516 /\
  (forall i : nat,
      (i < length a)%nat ->
      i <> 4%nat ->
      i <> 7%nat ->
      nth i result 0%Z = nth i a 0%Z).

Theorem UpdateElements_spec_satisfied
    (a : list Z)
    (h_precond : UpdateElements_precond a) :
  UpdateElements_postcond
    a (UpdateElements a h_precond) h_precond.
Admitted.
