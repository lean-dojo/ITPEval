(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.f_invert_permut (catalog title
  "permutation.f_invert_permut"): a bounded natural-number permutation maps
  its recursively defined inverse lookup back to every index in the bounded
  initial segment. This file contains no proof.
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

Theorem f_invert_permut :
  forall (f : nat -> nat) (n m : nat),
    m <= n ->
    logipedia_permutation_permut f n ->
    f (logipedia_permutation_invert_permut n f m) = m.
Admitted.
