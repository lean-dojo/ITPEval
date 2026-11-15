(* Statement-only formalization of PutnamBench corpus artifact putnam_2007_b6:
   the number of unordered factorial-coin representations of n! and its
   two-sided asymptotic bounds. This file contains no proof. *)

From Stdlib Require Import
  Reals Lists.List Sorting.Sorted Arith.PeanoNat Arith.Factorial.

Open Scope R_scope.

Definition putnam_2007_b6_has_cardinality
    {A : Type} (P : A -> Prop) (n : nat) : Prop :=
  exists xs : list A,
    NoDup xs /\
    (forall x : A, In x xs <-> P x) /\
    length xs = n.

Definition putnam_2007_b6_coin_collection
    (n : nat) (coins : list nat) : Prop :=
  Sorted Nat.le coins /\
  fold_right Nat.add 0%nat coins = fact n /\
  forall m : nat,
    In m coins ->
    exists k : nat,
      (1 <= k <= n)%nat /\
      m = fact k.

Theorem putnam_2007_b6
    (f : nat -> nat)
    (hf : forall n : nat,
      putnam_2007_b6_has_cardinality
        (putnam_2007_b6_coin_collection n) (f n)) :
  exists C : R,
    forall n : nat,
      (2 <= n)%nat ->
      Rpower (INR n) ((INR n) ^ 2 / 2 - C * INR n) *
        exp (- ((INR n) ^ 2) / 4) <= INR (f n) /\
      INR (f n) <=
        Rpower (INR n) ((INR n) ^ 2 / 2 + C * INR n) *
          exp (- ((INR n) ^ 2) / 4).
Admitted.
