(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.permut_to_bijn (catalog title "permutation.permut_to_bijn"):
  a natural-number function that maps an initial segment into itself and is
  injective there is surjective on that segment. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition injn (f : nat -> nat) (n : nat) : Prop :=
  forall i j : nat,
    i <= n ->
    j <= n ->
    f i = f j ->
    i = j.

Definition permut (f : nat -> nat) (n : nat) : Prop :=
  (forall i : nat, i <= n -> f i <= n) /\
  injn f n.

Definition bijn (f : nat -> nat) (n : nat) : Prop :=
  forall m : nat,
    m <= n ->
    exists p : nat, p <= n /\ f p = m.

Theorem permut_to_bijn :
  forall (n : nat) (f : nat -> nat),
    permut f n ->
    bijn f n.
Admitted.
