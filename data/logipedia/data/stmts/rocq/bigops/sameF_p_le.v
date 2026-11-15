(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sameF_p_le: filtered pointwise agreement below a natural-number
  bound is preserved when the bound is decreased. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition sameF_p {A : Type}
    (k : nat) (p : nat -> bool) (f g : nat -> A) : Prop :=
  forall i : nat,
    i < k ->
    p i = true ->
    f i = g i.

Theorem bigops_sameF_p_le :
  forall (A : Type)
         (p : nat -> bool)
         (f g : nat -> A)
         (n m : nat),
    n <= m ->
    sameF_p m p f g ->
    sameF_p n p f g.
Admitted.
