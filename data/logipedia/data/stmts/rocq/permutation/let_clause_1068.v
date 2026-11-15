(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.let_clause_1068 (catalog title
  "permutation.let_clause_1068"): a bounded natural-number permutation
  statement whose premises include image equations for two equal indices,
  concluding the first stated image equation. This file contains no proof.
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

Theorem let_clause_1068 :
  forall (f : nat -> nat) (n : nat),
    logipedia_permutation_permut f n ->
    forall i j : nat,
      i <= n ->
      j <= n ->
      forall a : nat,
        (a <= n /\ f a = i) ->
        a <= n ->
        f a = i ->
        forall b : nat,
          (b <= n /\ f b = j) ->
          b <= n ->
          f b = j ->
          (forall i0 : nat, i0 <= n -> f i0 <= n) ->
          logipedia_permutation_injn f n ->
          a = b ->
          f a = i.
Admitted.
