(*
  Statement-only formalization of "Brouwer Fixed Point Theorem" from Hundred Theorems item 036.
  This file contains no proof.
*)

(* Hundred Theorems corpus: Brouwer Fixed Point Theorem.
   Subject: fixed points of continuous self-maps of compact convex subsets
   of finite-dimensional real Euclidean space.
   Statement-only encoding; no proof is provided. *)

From Stdlib Require Import Vectors.Fin Reals.

Local Open Scope R_scope.

Definition euclidean_point (n : nat) : Type := Fin.t n -> R.

Definition euclidean_set (n : nat) : Type := euclidean_point n -> Prop.

Definition pointwise_equal {n : nat}
    (x y : euclidean_point n) : Prop :=
  forall i : Fin.t n, x i = y i.

Definition euclidean_close {n : nat}
    (x y : euclidean_point n) (epsilon : R) : Prop :=
  forall i : Fin.t n, Rabs (x i - y i) < epsilon.

Definition euclidean_converges {n : nat}
    (u : nat -> euclidean_point n) (x : euclidean_point n) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall k : nat,
        (N <= k)%nat ->
        euclidean_close (u k) x epsilon.

Definition strictly_increasing (r : nat -> nat) : Prop :=
  forall i j : nat,
    (i < j)%nat ->
    (r i < r j)%nat.

Definition compact_euclidean_set {n : nat}
    (K : euclidean_set n) : Prop :=
  forall u : nat -> euclidean_point n,
    (forall k : nat, K (u k)) ->
    exists r : nat -> nat,
      strictly_increasing r /\
      exists x : euclidean_point n,
        K x /\
        euclidean_converges (fun k => u (r k)) x.

Definition convex_euclidean_set {n : nat}
    (K : euclidean_set n) : Prop :=
  forall x y : euclidean_point n,
    K x ->
    K y ->
    forall t : R,
      0 <= t /\ t <= 1 ->
      K (fun i => (1 - t) * x i + t * y i).

Definition continuous_on_euclidean_set {n : nat}
    (K : euclidean_set n)
    (f : euclidean_point n -> euclidean_point n) : Prop :=
  forall x : euclidean_point n,
    K x ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall y : euclidean_point n,
          K y ->
          euclidean_close x y delta ->
          euclidean_close (f x) (f y) epsilon.

Theorem brouwer_fixed_point :
  forall (dimension_index : nat)
         (K : euclidean_set (S dimension_index))
         (f : euclidean_point (S dimension_index) ->
              euclidean_point (S dimension_index)),
    compact_euclidean_set K ->
    convex_euclidean_set K ->
    (exists x : euclidean_point (S dimension_index), K x) ->
    continuous_on_euclidean_set K f ->
    (forall x : euclidean_point (S dimension_index), K x -> K (f x)) ->
    exists x : euclidean_point (S dimension_index),
      K x /\ pointwise_equal (f x) x.
Proof.
Admitted.
