(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1134776
  (thousand-theorems__rocq__Q1134776), "Dilworth's theorem": for every finite
  partial order, the minimum size of a partition into chains equals the
  maximum size of an antichain. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1134776_partial_order (A : Type) : Type := {
  q1134776_le : A -> A -> Prop;
  q1134776_le_refl :
    forall x : A, q1134776_le x x;
  q1134776_le_antisym :
    forall x y : A,
      q1134776_le x y ->
      q1134776_le y x ->
      x = y;
  q1134776_le_trans :
    forall x y z : A,
      q1134776_le x y ->
      q1134776_le y z ->
      q1134776_le x z
}.

Arguments q1134776_le {A} _ _ _.

Definition q1134776_injective
    {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition q1134776_surjective
    {A B : Type} (f : A -> B) : Prop :=
  forall y : B, exists x : A, f x = y.

Definition q1134776_finite_type (A : Type) : Prop :=
  exists (n : nat) (enumeration : Fin.t n -> A),
    q1134776_injective enumeration /\
    q1134776_surjective enumeration.

Definition q1134776_chain_partition_size
    {A : Type}
    (P : q1134776_partial_order A)
    (n : nat) : Prop :=
  exists color : A -> Fin.t n,
    q1134776_surjective color /\
    forall (i : Fin.t n) (x y : A),
      color x = i ->
      color y = i ->
      q1134776_le P x y \/ q1134776_le P y x.

Definition q1134776_antichain_size
    {A : Type}
    (P : q1134776_partial_order A)
    (n : nat) : Prop :=
  exists elements : Fin.t n -> A,
    q1134776_injective elements /\
    forall i j : Fin.t n,
      i <> j ->
      ~ q1134776_le P (elements i) (elements j) /\
      ~ q1134776_le P (elements j) (elements i).

Definition q1134776_is_min_chain_partition_size
    {A : Type}
    (P : q1134776_partial_order A)
    (n : nat) : Prop :=
  q1134776_chain_partition_size P n /\
  forall m : nat,
    q1134776_chain_partition_size P m ->
    (n <= m)%nat.

Definition q1134776_is_antichain_width
    {A : Type}
    (P : q1134776_partial_order A)
    (n : nat) : Prop :=
  q1134776_antichain_size P n /\
  forall m : nat,
    q1134776_antichain_size P m ->
    (m <= n)%nat.

Theorem minChainPartition_eq_antichainWidth :
  forall (A : Type) (P : q1134776_partial_order A),
    q1134776_finite_type A ->
    exists n : nat,
      q1134776_is_min_chain_partition_size P n /\
      q1134776_is_antichain_width P n.
Admitted.
