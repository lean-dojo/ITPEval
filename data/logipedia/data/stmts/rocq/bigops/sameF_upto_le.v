(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sameF_upto_le: pointwise agreement below a natural-number bound is
  preserved when the bound is decreased. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition sameF_upto {A : Type}
    (k : nat) (f g : nat -> A) : Prop :=
  forall i : nat,
    i < k ->
    f i = g i.

Theorem bigops_sameF_upto_le :
  forall (A : Type)
         (f g : nat -> A)
         (n m : nat),
    n <= m ->
    sameF_upto m f g ->
    sameF_upto n f g.
Admitted.
