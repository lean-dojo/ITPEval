(* Statement-only formalization of VERINA corpus artifact verina_basic_33,
   catalog title "smallestMissingNumber": a deterministic scan of a
   nondecreasing list of natural numbers for the least missing natural,
   together with its missingness, minimality, and final correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Fixpoint smallestMissingNumber_pairwise_le (s : list nat) : Prop :=
  match s with
  | [] => True
  | x :: xs =>
      Forall (fun y => Nat.le x y) xs /\
      smallestMissingNumber_pairwise_le xs
  end.

Definition smallestMissingNumber_precond (s : list nat) : Prop :=
  smallestMissingNumber_pairwise_le s.

Fixpoint smallestMissingNumber_findMissing
    (v : nat) (l : list nat) : nat :=
  match l with
  | [] => v
  | x :: xs =>
      if Nat.ltb v x
      then v
      else if Nat.eqb x v
      then smallestMissingNumber_findMissing (Nat.add v 1) xs
      else smallestMissingNumber_findMissing v xs
  end.

Definition smallestMissingNumber
    (s : list nat)
    (_h_precond : smallestMissingNumber_precond s) : nat :=
  smallestMissingNumber_findMissing 0 s.

Definition smallestMissingNumber_postcond
    (s : list nat)
    (result : nat)
    (_h_precond : smallestMissingNumber_precond s) : Prop :=
  ~ In result s /\
  forall k : nat,
    Nat.lt k result ->
    In k s.

Theorem smallestMissingNumber_spec_satisfied
    (s : list nat)
    (h_precond : smallestMissingNumber_precond s) :
  smallestMissingNumber_postcond
    s
    (smallestMissingNumber s h_precond)
    h_precond.
Admitted.
