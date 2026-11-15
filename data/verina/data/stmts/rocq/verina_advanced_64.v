(* Statement-only formalization of VERINA corpus artifact verina_advanced_64,
   catalog title "removeElement": an executable list traversal that removes
   every occurrence of a target natural number while preserving the order of
   all remaining elements, together with its indexed filtering correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition removeElement_precond
    (_lst : list nat)
    (_target : nat) : Prop :=
  True.

Fixpoint removeElement_helper
    (lst : list nat)
    (target : nat) : list nat :=
  match lst with
  | [] => []
  | x :: xs =>
      let rest := removeElement_helper xs target in
      if Nat.eqb x target then rest else x :: rest
  end.

Definition removeElement
    (lst : list nat)
    (target : nat)
    (_h_precond : removeElement_precond lst target) : list nat :=
  removeElement_helper lst target.

Fixpoint removeElement_zipIdxFrom
    (lst : list nat)
    (index : nat) : list (nat * nat) :=
  match lst with
  | [] => []
  | x :: xs =>
      (x, index) :: removeElement_zipIdxFrom xs (S index)
  end.

Definition removeElement_zipIdx
    (lst : list nat) : list (nat * nat) :=
  removeElement_zipIdxFrom lst 0%nat.

Definition removeElement_postcond
    (lst : list nat)
    (target : nat)
    (result : list nat)
    (_h_precond : removeElement_precond lst target) : Prop :=
  let filtered :=
    filter (fun x => negb (Nat.eqb x target)) lst in
  forallb
    (fun indexed =>
      match nth_error filtered (snd indexed) with
      | Some y => Nat.eqb (fst indexed) y
      | None => false
      end)
    (removeElement_zipIdx result) = true /\
  length result = length filtered.

Theorem removeElement_spec_satisfied
    (lst : list nat)
    (target : nat)
    (h_precond : removeElement_precond lst target) :
  removeElement_postcond
    lst target (removeElement lst target h_precond) h_precond.
Admitted.
