(* Statement-only formalization of VERINA corpus artifact verina_advanced_73,
   catalog title "smallestMissing": a deterministic scan of a strictly
   increasing list of natural numbers for the least missing natural, together
   with its missingness and minimality correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Fixpoint smallestMissing_pairwise_lt (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
      Forall (fun y => Nat.lt x y) xs /\
      smallestMissing_pairwise_lt xs
  end.

Definition smallestMissing_precond (l : list nat) : Prop :=
  smallestMissing_pairwise_lt l.

Fixpoint smallestMissing_search (lst : list nat) (n : nat) : nat :=
  match lst with
  | [] => n
  | x :: xs =>
      if Nat.eqb x n
      then smallestMissing_search xs (Nat.add n 1)
      else if Nat.ltb n x
      then n
      else smallestMissing_search xs n
  end.

Definition smallestMissing
    (l : list nat)
    (_h_precond : smallestMissing_precond l) : nat :=
  smallestMissing_search l 0.

Definition smallestMissing_postcond
    (l : list nat)
    (result : nat)
    (_h_precond : smallestMissing_precond l) : Prop :=
  ~ In result l /\
  forall candidate : nat,
    Nat.lt candidate result ->
    In candidate l.

Theorem smallestMissing_spec_satisfied
    (l : list nat)
    (h_precond : smallestMissing_precond l) :
  smallestMissing_postcond
    l
    (smallestMissing l h_precond)
    h_precond.
Admitted.
