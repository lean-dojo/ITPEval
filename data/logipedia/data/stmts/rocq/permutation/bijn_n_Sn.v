(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_n_Sn (catalog title "permutation.bijn_n_Sn"): bounded
  surjectivity on a natural-number initial segment extends to its successor
  when the new endpoint is fixed. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition bijn (f : nat -> nat) (n : nat) : Prop :=
  forall m : nat,
    m <= n ->
    exists p : nat, p <= n /\ f p = m.

Theorem bijn_n_Sn :
  forall (f : nat -> nat) (n : nat),
    bijn f n ->
    f (S n) = S n ->
    bijn f (S n).
Admitted.
