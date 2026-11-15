(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injective_invert_permut (catalog title
  "permutation.injective_invert_permut"): the recursively defined inverse of
  a bounded natural-number permutation is injective on the same initial
  segment. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_permutation_injn
    (f : nat -> nat) (n : nat) : Prop :=
  forall i j : nat,
    i <= n ->
    j <= n ->
    f i = f j ->
    i = j.

Definition logipedia_permutation_permut
    (f : nat -> nat) (n : nat) : Prop :=
  (forall i : nat, i <= n -> f i <= n) /\
  logipedia_permutation_injn f n.

Fixpoint logipedia_permutation_invert_permut
    (n : nat) (f : nat -> nat) (m : nat) : nat :=
  match n with
  | O => O
  | S k =>
      if Nat.eqb m (f (S k))
      then S k
      else logipedia_permutation_invert_permut k f m
  end.

Theorem injective_invert_permut :
  forall (f : nat -> nat) (n : nat),
    logipedia_permutation_permut f n ->
    logipedia_permutation_injn
      (logipedia_permutation_invert_permut n f) n.
Admitted.
