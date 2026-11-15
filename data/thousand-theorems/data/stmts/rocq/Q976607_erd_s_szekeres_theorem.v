(*
  Statement-only formalization of Thousand Theorems corpus artifact Q976607
  (thousand-theorems__rocq__Q976607), "Erdős–Szekeres theorem": an injective
  map from a finite linearly ordered type into a linearly ordered type has,
  when the domain has more than r * s elements, a finite subset of size
  greater than r on which it is strictly increasing or one of size greater
  than s on which it is strictly decreasing. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q976607_linear_order (A : Type) : Type := {
  q976607_le : A -> A -> Prop;
  q976607_le_refl :
    forall x : A, q976607_le x x;
  q976607_le_trans :
    forall x y z : A,
      q976607_le x y ->
      q976607_le y z ->
      q976607_le x z;
  q976607_le_antisym :
    forall x y : A,
      q976607_le x y ->
      q976607_le y x ->
      x = y;
  q976607_le_total :
    forall x y : A,
      q976607_le x y \/ q976607_le y x;
  q976607_le_decidable :
    forall x y : A,
      {q976607_le x y} + {~ q976607_le x y}
}.

Arguments q976607_le {A} _ _ _.

Definition q976607_lt
    {A : Type} (O : q976607_linear_order A) (x y : A) : Prop :=
  q976607_le O x y /\ ~ q976607_le O y x.

Record q976607_finite_type (A : Type) : Type := {
  q976607_enumeration : list A;
  q976607_enumeration_nodup : NoDup q976607_enumeration;
  q976607_enumeration_complete :
    forall x : A, In x q976607_enumeration
}.

Arguments q976607_enumeration {A} _.

Record q976607_finset (A : Type) : Type := {
  q976607_elements : list A;
  q976607_elements_nodup : NoDup q976607_elements
}.

Arguments q976607_elements {A} _.

Definition q976607_mem
    {A : Type} (x : A) (t : q976607_finset A) : Prop :=
  In x (q976607_elements t).

Definition q976607_injective
    {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition q976607_strict_mono_on
    {A B : Type}
    (OA : q976607_linear_order A)
    (OB : q976607_linear_order B)
    (f : A -> B)
    (t : q976607_finset A) : Prop :=
  forall x y : A,
    q976607_mem x t ->
    q976607_mem y t ->
    q976607_lt OA x y ->
    q976607_lt OB (f x) (f y).

Definition q976607_strict_anti_on
    {A B : Type}
    (OA : q976607_linear_order A)
    (OB : q976607_linear_order B)
    (f : A -> B)
    (t : q976607_finset A) : Prop :=
  forall x y : A,
    q976607_mem x t ->
    q976607_mem y t ->
    q976607_lt OA x y ->
    q976607_lt OB (f y) (f x).

Module Theorems100.

Theorem erdos_szekeres :
  forall (A B : Type)
         (OA : q976607_linear_order A)
         (OB : q976607_linear_order B)
         (FA : q976607_finite_type A)
         (r s : nat)
         (f : A -> B),
    (r * s < length (q976607_enumeration FA))%nat ->
    q976607_injective f ->
    (exists t : q976607_finset A,
      (r < length (q976607_elements t))%nat /\
      q976607_strict_mono_on OA OB f t) \/
    exists t : q976607_finset A,
      (s < length (q976607_elements t))%nat /\
      q976607_strict_anti_on OA OB f t.
Admitted.

End Theorems100.
