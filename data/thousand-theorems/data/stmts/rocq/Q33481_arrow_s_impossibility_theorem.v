(*
  Statement-only formalization of Thousand Theorems corpus artifact Q33481
  (thousand-theorems__rocq__Q33481), "Arrow's impossibility theorem":
  for at least three alternatives and finitely many voters, every social
  welfare function on total preorders satisfying weak Pareto and independence
  of irrelevant alternatives is a dictatorship. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Set Universe Polymorphism.
Set Implicit Arguments.

Polymorphic Record q33481_preference_order@{u}
    (A : Type@{u}) : Type@{u+1} := {
  q33481_preferred_or_tied : A -> A -> Prop;
  q33481_preference_refl :
    forall x : A, q33481_preferred_or_tied x x;
  q33481_preference_total :
    forall x y : A,
      q33481_preferred_or_tied x y \/
      q33481_preferred_or_tied y x;
  q33481_preference_trans :
    forall x y z : A,
      q33481_preferred_or_tied x y ->
      q33481_preferred_or_tied y z ->
      q33481_preferred_or_tied x z
}.

Arguments q33481_preferred_or_tied {A} _ _ _.

Polymorphic Definition q33481_strictly_prefers@{u}
    {A : Type@{u}}
    (R : q33481_preference_order A)
    (x y : A) : Prop :=
  q33481_preferred_or_tied R x y /\
  ~ q33481_preferred_or_tied R y x.

Polymorphic Record q33481_finset@{u} (A : Type@{u}) : Type@{u+1} := {
  q33481_finset_elements : list A;
  q33481_finset_nodup : NoDup q33481_finset_elements
}.

Arguments q33481_finset_elements {A} _.

Polymorphic Definition q33481_mem@{u}
    {A : Type@{u}} (x : A) (X : q33481_finset A) : Prop :=
  In x (q33481_finset_elements X).

Polymorphic Definition q33481_card@{u}
    {A : Type@{u}} (X : q33481_finset A) : nat :=
  length (q33481_finset_elements X).

Polymorphic Record q33481_finite_type@{u}
    (I : Type@{u}) : Type@{u+1} := {
  q33481_enumeration : list I;
  q33481_enumeration_nodup : NoDup q33481_enumeration;
  q33481_enumeration_complete :
    forall i : I, In i q33481_enumeration
}.

Polymorphic Definition q33481_same_pair_order@{u}
    {A : Type@{u}}
    (R R' : q33481_preference_order A)
    (x y : A) : Prop :=
  (q33481_strictly_prefers R x y <->
   q33481_strictly_prefers R' x y) /\
  (q33481_strictly_prefers R y x <->
   q33481_strictly_prefers R' y x).

Polymorphic Definition q33481_weak_pareto@{u v}
    {A : Type@{u}}
    {I : Type@{v}}
    (f : (I -> q33481_preference_order A) ->
         q33481_preference_order A)
    (X : q33481_finset A) : Prop :=
  forall (x y : A),
    q33481_mem x X ->
    q33481_mem y X ->
    forall R : I -> q33481_preference_order A,
      (forall i : I, q33481_strictly_prefers (R i) x y) ->
      q33481_strictly_prefers (f R) x y.

Polymorphic Definition q33481_independence_of_irrelevant_alternatives@{u v}
    {A : Type@{u}}
    {I : Type@{v}}
    (f : (I -> q33481_preference_order A) ->
         q33481_preference_order A)
    (X : q33481_finset A) : Prop :=
  forall (R R' : I -> q33481_preference_order A)
         (x y : A),
    q33481_mem x X ->
    q33481_mem y X ->
    (forall i : I, q33481_same_pair_order (R i) (R' i) x y) ->
    q33481_same_pair_order (f R) (f R') x y.

Polymorphic Definition q33481_is_dictatorship@{u v}
    {A : Type@{u}}
    {I : Type@{v}}
    (f : (I -> q33481_preference_order A) ->
         q33481_preference_order A)
    (X : q33481_finset A) : Prop :=
  exists i : I,
    forall (x y : A),
      q33481_mem x X ->
      q33481_mem y X ->
      forall R : I -> q33481_preference_order A,
        q33481_strictly_prefers (R i) x y ->
        q33481_strictly_prefers (f R) x y.

Polymorphic Theorem arrow@{u v} :
  forall (A : Type@{u})
         (I : Type@{v})
         (_ : q33481_finite_type I)
         (X : q33481_finset A)
         (f : (I -> q33481_preference_order A) ->
              q33481_preference_order A),
    q33481_weak_pareto f X ->
    q33481_independence_of_irrelevant_alternatives f X ->
    (3 <= q33481_card X)%nat ->
    q33481_is_dictatorship f X.
Admitted.
