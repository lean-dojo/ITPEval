(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.invert_permut_f (catalog title
  "permutation.invert_permut_f"): a recursively defined inverse lookup for a
  bounded injective natural-number function returns each index when applied
  to its image. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_permutation_injn
    (f : nat -> nat) (n : nat) : Prop :=
  forall i j : nat,
    i <= n ->
    j <= n ->
    f i = f j ->
    i = j.

Fixpoint logipedia_permutation_invert_permut
    (n : nat) (f : nat -> nat) (m : nat) : nat :=
  match n with
  | O => O
  | S k =>
      if Nat.eqb m (f (S k))
      then S k
      else logipedia_permutation_invert_permut k f m
  end.

Theorem invert_permut_f :
  forall (f : nat -> nat) (n m : nat),
    m <= n ->
    logipedia_permutation_injn f n ->
    logipedia_permutation_invert_permut n f (f m) = m.
Admitted.
