(*
  Statement-only formalization of Thousand Theorems corpus artifact Q257387
  (thousand-theorems__rocq__Q257387), "Vitali theorem": a classically chosen
  transversal in [0,1] for equivalence modulo rational translation is not
  measurable in the standard Borel sigma-algebra on the real line. This file
  contains no proof.
*)

From Stdlib Require Import Reals QArith ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q257387_set (A : Type) : Type := A -> Prop.

Definition q257387_empty {A : Type} : q257387_set A :=
  fun _ => False.

Definition q257387_complement {A : Type}
    (E : q257387_set A) : q257387_set A :=
  fun x => ~ E x.

Definition q257387_countable_union {A : Type}
    (E : nat -> q257387_set A) : q257387_set A :=
  fun x => exists n : nat, E n x.

Definition q257387_same_set {A : Type}
    (E F : q257387_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q257387_open_real_set
    (U : q257387_set R) : Prop :=
  forall x : R,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : R, Rabs (y - x) < radius -> U y.

Definition q257387_sigma_class {A : Type}
    (C : q257387_set (q257387_set A)) : Prop :=
  C q257387_empty /\
  (forall E F : q257387_set A,
    q257387_same_set E F ->
    C E ->
    C F) /\
  (forall E : q257387_set A,
    C E ->
    C (q257387_complement E)) /\
  (forall E : nat -> q257387_set A,
    (forall n : nat, C (E n)) ->
    C (q257387_countable_union E)).

Definition q257387_borel_set
    (E : q257387_set R) : Prop :=
  forall C : q257387_set (q257387_set R),
    q257387_sigma_class C ->
    (forall U : q257387_set R,
      q257387_open_real_set U ->
      C U) ->
    C E.

Definition q257387_unit_interval
    (x : R) : Prop :=
  0 <= x /\ x <= 1.

Definition q257387_rational_equivalent
    (x y : R) : Prop :=
  exists q : Q, x - y = Q2R q.

Definition q257387_is_vitali_selector
    (V : q257387_set R) : Prop :=
  (forall y : R,
    V y ->
    q257387_unit_interval y) /\
  (forall x : R,
    q257387_unit_interval x ->
    exists y : R,
      V y /\
      q257387_rational_equivalent x y) /\
  (forall y z : R,
    V y ->
    V z ->
    q257387_rational_equivalent y z ->
    y = z).

Definition q257387_vitaliSet : q257387_set R :=
  epsilon
    (inhabits (fun _ : R => False))
    q257387_is_vitali_selector.

Theorem vitaliSet_not_measurable :
  ~ q257387_borel_set q257387_vitaliSet.
Admitted.
