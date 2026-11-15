(* Statement-only formalization of VERINA corpus artifact verina_advanced_5,
   catalog title "addTwoNumbers": executable digit-wise addition of two
   nonempty reverse-order base-10 natural-number lists, together with its
   canonical-digit correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Fixpoint listToNat (digits : list nat) : nat :=
  match digits with
  | [] => 0%nat
  | d :: ds => d + 10 * listToNat ds
  end.

Definition addTwoNumbers_precond
    (l1 l2 : list nat) : Prop :=
  (0 < length l1)%nat /\
  (0 < length l2)%nat /\
  (forall d : nat, In d l1 -> (d < 10)%nat) /\
  (forall d : nat, In d l2 -> (d < 10)%nat) /\
  (last l1 0%nat <> 0%nat \/ l1 = [0%nat]) /\
  (last l2 0%nat <> 0%nat \/ l2 = [0%nat]).

Fixpoint addTwoNumbers_addRight
    (l2 : list nat) (carry : nat) : list nat :=
  match l2 with
  | [] =>
      if Nat.eqb carry 0%nat then [] else [carry]
  | h2 :: t2 =>
      let sum := h2 + carry in
      Nat.modulo sum 10%nat
        :: addTwoNumbers_addRight t2 (Nat.div sum 10%nat)
  end.

Fixpoint addTwoNumbers_addAux
    (l1 l2 : list nat) (carry : nat) : list nat :=
  match l1 with
  | [] => addTwoNumbers_addRight l2 carry
  | h1 :: t1 =>
      match l2 with
      | [] =>
          let sum := h1 + carry in
          Nat.modulo sum 10%nat
            :: addTwoNumbers_addAux t1 [] (Nat.div sum 10%nat)
      | h2 :: t2 =>
          let sum := h1 + h2 + carry in
          Nat.modulo sum 10%nat
            :: addTwoNumbers_addAux t1 t2 (Nat.div sum 10%nat)
      end
  end.

Definition addTwoNumbers
    (l1 l2 : list nat)
    (_h_precond : addTwoNumbers_precond l1 l2) : list nat :=
  addTwoNumbers_addAux l1 l2 0%nat.

Definition addTwoNumbers_postcond
    (l1 l2 result : list nat)
    (_h_precond : addTwoNumbers_precond l1 l2) : Prop :=
  listToNat result = listToNat l1 + listToNat l2 /\
  (forall d : nat, In d result -> (d < 10)%nat) /\
  (last result 0%nat <> 0%nat \/
    (l1 = [0%nat] /\ l2 = [0%nat] /\ result = [0%nat])).

Theorem addTwoNumbers_spec_satisfied
    (l1 l2 : list nat)
    (h_precond : addTwoNumbers_precond l1 l2) :
  addTwoNumbers_postcond
    l1 l2 (addTwoNumbers l1 l2 h_precond) h_precond.
Admitted.
