(*
  Statement-only formalization of Thousand Theorems corpus artifact Q752375
  (thousand-theorems__rocq__Q752375), "Extreme value theorem": a continuous
  function from a nonempty compact subset of an arbitrary topological space
  into a linearly ordered topological space with closed lower intervals
  attains its minimum on that set. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q752375_set (A : Type) : Type := A -> Prop.

Definition q752375_subset
    {A : Type}
    (U V : q752375_set A) : Prop :=
  forall x : A, U x -> V x.

Record q752375_linear_order (A : Type) : Type := {
  q752375_le : A -> A -> Prop;
  q752375_le_refl :
    forall x : A, q752375_le x x;
  q752375_le_antisym :
    forall x y : A,
      q752375_le x y -> q752375_le y x -> x = y;
  q752375_le_trans :
    forall x y z : A,
      q752375_le x y -> q752375_le y z -> q752375_le x z;
  q752375_le_total :
    forall x y : A, q752375_le x y \/ q752375_le y x
}.

Arguments q752375_le {A} _ _ _.

Record q752375_topological_space (A : Type) : Type := {
  q752375_is_open : q752375_set A -> Prop;
  q752375_open_ext :
    forall U V : q752375_set A,
      (forall x : A, U x <-> V x) ->
      (q752375_is_open U <-> q752375_is_open V);
  q752375_open_univ :
    q752375_is_open (fun _ : A => True);
  q752375_open_inter :
    forall U V : q752375_set A,
      q752375_is_open U ->
      q752375_is_open V ->
      q752375_is_open (fun x : A => U x /\ V x);
  q752375_open_sUnion :
    forall family : q752375_set (q752375_set A),
      (forall U : q752375_set A,
        family U -> q752375_is_open U) ->
      q752375_is_open
        (fun x : A =>
          exists U : q752375_set A, family U /\ U x)
}.

Arguments q752375_is_open {A} _ _.

Definition q752375_is_closed
    {A : Type}
    (T : q752375_topological_space A)
    (C : q752375_set A) : Prop :=
  q752375_is_open T (fun x : A => ~ C x).

Definition q752375_closed_iic_topology
    {A : Type}
    (O : q752375_linear_order A)
    (T : q752375_topological_space A) : Prop :=
  forall a : A,
    q752375_is_closed T
      (fun x : A => q752375_le O x a).

Definition q752375_neighborhood
    {A : Type}
    (T : q752375_topological_space A)
    (x : A)
    (U : q752375_set A) : Prop :=
  exists V : q752375_set A,
    q752375_is_open T V /\
    V x /\
    q752375_subset V U.

Definition q752375_is_compact
    {A : Type}
    (T : q752375_topological_space A)
    (K : q752375_set A) : Prop :=
  forall cover : q752375_set (q752375_set A),
    (forall U : q752375_set A,
      cover U -> q752375_is_open T U) ->
    (forall x : A,
      K x ->
      exists U : q752375_set A, cover U /\ U x) ->
    exists finite_cover : list (q752375_set A),
      Forall cover finite_cover /\
      forall x : A,
        K x ->
        exists U : q752375_set A,
          In U finite_cover /\ U x.

Definition q752375_continuous_within_at
    {A B : Type}
    (TA : q752375_topological_space A)
    (TB : q752375_topological_space B)
    (f : A -> B)
    (s : q752375_set A)
    (x : A) : Prop :=
  forall V : q752375_set B,
    q752375_neighborhood TB (f x) V ->
    exists U : q752375_set A,
      q752375_neighborhood TA x U /\
      forall y : A, s y -> U y -> V (f y).

Definition q752375_continuous_on
    {A B : Type}
    (TA : q752375_topological_space A)
    (TB : q752375_topological_space B)
    (f : A -> B)
    (s : q752375_set A) : Prop :=
  forall x : A,
    s x ->
    q752375_continuous_within_at TA TB f s x.

Theorem extreme_value_theorem :
  forall (Alpha Beta : Type)
         (OA : q752375_linear_order Alpha)
         (TA : q752375_topological_space Alpha)
         (TB : q752375_topological_space Beta)
         (ClosedIicA : q752375_closed_iic_topology OA TA)
         (s : q752375_set Beta)
         (f : Beta -> Alpha),
    q752375_is_compact TB s ->
    (exists x : Beta, s x) ->
    q752375_continuous_on TB TA f s ->
    exists x : Beta,
      s x /\
      forall y : Beta,
        s y -> q752375_le OA (f x) (f y).
Admitted.
