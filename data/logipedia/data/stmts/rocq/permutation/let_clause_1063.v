(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.let_clause_1063 (catalog title
  "permutation.let_clause_1063"): equality of two indices in a bounded
  natural-number permutation transfers the second index's image equation to
  the first index. This file contains no proof.
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

Theorem let_clause_1063 :
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
          f a = j.
Admitted.
