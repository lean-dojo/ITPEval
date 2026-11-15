(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_transpose, catalog title "permutation.bijn_transpose":
  a transposition of two natural numbers bounded by n is surjective on the
  natural numbers bounded by n. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_permutation_transpose
    (i j k : nat) : nat :=
  if Nat.eqb k i then j
  else if Nat.eqb k j then i
  else k.

Definition logipedia_permutation_bijn
    (f : nat -> nat) (n : nat) : Prop :=
  forall m : nat,
    Nat.le m n ->
    exists p : nat,
      Nat.le p n /\ f p = m.

Theorem bijn_transpose :
  forall n i j : nat,
    Nat.le i n ->
    Nat.le j n ->
    logipedia_permutation_bijn
      (logipedia_permutation_transpose i j) n.
Proof.
Admitted.
