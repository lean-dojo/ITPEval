(* Statement-only formalization of VERINA corpus artifact verina_basic_2,
   catalog title "findSmallest": an executable option-valued minimum
   computation for a natural-number array, together with its empty-case,
   membership, and least-element correctness contract. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Definition findSmallest_precond (_s : list nat) : Prop :=
  True.

Fixpoint findSmallest_min (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | x :: rest =>
      match findSmallest_min rest with
      | None => Some x
      | Some current => Some (Nat.min x current)
      end
  end.

Definition findSmallest
    (s : list nat)
    (_h_precond : findSmallest_precond s) : option nat :=
  findSmallest_min s.

Definition findSmallest_postcond
    (s : list nat)
    (result : option nat)
    (_h_precond : findSmallest_precond s) : Prop :=
  match result with
  | None => s = []
  | Some r =>
      In r s /\
      forall x : nat, In x s -> Nat.le r x
  end.

Theorem findSmallest_spec_satisfied
    (s : list nat)
    (h_precond : findSmallest_precond s) :
  findSmallest_postcond
    s (findSmallest s h_precond) h_precond.
Admitted.
