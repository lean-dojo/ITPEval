(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_fg (catalog title "permutation.bijn_fg"): bounded
  surjectivity of natural-number functions on an initial segment is
  preserved under composition. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition bijn (f : nat -> nat) (n : nat) : Prop :=
  forall m : nat,
    m <= n ->
    exists p : nat, p <= n /\ f p = m.

Theorem bijn_fg :
  forall (f g : nat -> nat) (n : nat),
    bijn f n ->
    bijn g n ->
    bijn (fun p : nat => f (g p)) n.
Admitted.
