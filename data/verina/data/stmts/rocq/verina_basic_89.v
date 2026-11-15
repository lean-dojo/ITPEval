(* Statement-only formalization of VERINA corpus artifact verina_basic_89,
   catalog title "SetToSeq": executable stable first-occurrence
   deduplication of an arbitrary integer list, together with its
   unconditional precondition, membership, uniqueness, and order-preservation
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Module VerinaBasic89.

Definition SetToSeq_precond (_s : list Z) : Prop :=
  True.

Definition SetToSeq_step
    (acc : list Z)
    (x : Z) : list Z :=
  if existsb (Z.eqb x) acc
  then acc
  else acc ++ [x].

Definition SetToSeq
    (s : list Z)
    (_h_precond : SetToSeq_precond s) : list Z :=
  fold_left SetToSeq_step s [].

Fixpoint SetToSeq_idxOf
    (x : Z)
    (xs : list Z) : nat :=
  match xs with
  | [] => 0%nat
  | y :: ys =>
      if Z.eqb x y
      then 0%nat
      else S (SetToSeq_idxOf x ys)
  end.

Inductive SetToSeq_pairwise
    {A : Type}
    (relation : A -> A -> Prop) : list A -> Prop :=
| SetToSeq_pairwise_nil :
    SetToSeq_pairwise relation []
| SetToSeq_pairwise_cons :
    forall (head : A) (tail : list A),
      Forall (relation head) tail ->
      SetToSeq_pairwise relation tail ->
      SetToSeq_pairwise relation (head :: tail).

Definition SetToSeq_postcond
    (s result : list Z)
    (_h_precond : SetToSeq_precond s) : Prop :=
  Forall (fun a => In a s) result /\
  Forall (fun a => In a result) s /\
  Forall
    (fun a => count_occ Z.eq_dec result a = 1%nat)
    result /\
  SetToSeq_pairwise
    (fun a b =>
      (SetToSeq_idxOf a result < SetToSeq_idxOf b result)%nat ->
      (SetToSeq_idxOf a s < SetToSeq_idxOf b s)%nat)
    result.

Theorem SetToSeq_spec_satisfied
    (s : list Z)
    (h_precond : SetToSeq_precond s) :
  SetToSeq_postcond
    s (SetToSeq s h_precond) h_precond.
Admitted.

End VerinaBasic89.
