(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_to_bijn (catalog title "permutation.eq_to_bijn"):
  bounded surjectivity on a natural-number initial segment is preserved when
  two functions agree throughout that segment. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition bijn (f : nat -> nat) (n : nat) : Prop :=
  forall m : nat,
    m <= n ->
    exists p : nat, p <= n /\ f p = m.

Theorem eq_to_bijn :
  forall (f g : nat -> nat) (n : nat),
    (forall i : nat, i <= n -> f i = g i) ->
    bijn f n ->
    bijn g n.
Admitted.
