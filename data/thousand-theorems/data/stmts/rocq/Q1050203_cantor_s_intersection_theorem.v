(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1050203
  (thousand-theorems__rocq__Q1050203), "Cantor's intersection theorem": the
  intersection of a nonempty downward-directed family of nonempty compact
  closed subsets of an arbitrary topological space is nonempty.
  This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q1050203_set (A : Type) : Type := A -> Prop.

Definition q1050203_same_set
    {A : Type}
    (U V : q1050203_set A) : Prop :=
  forall x : A, U x <-> V x.

Record q1050203_family (X : Type) : Type := {
  q1050203_member : q1050203_set X -> Prop;
  q1050203_member_ext :
    forall U V : q1050203_set X,
      q1050203_same_set U V ->
      (q1050203_member U <-> q1050203_member V)
}.

Arguments q1050203_member {X} _ _.

Record q1050203_topological_space (X : Type) : Type := {
  q1050203_is_open : q1050203_set X -> Prop;
  q1050203_open_ext :
    forall U V : q1050203_set X,
      q1050203_same_set U V ->
      (q1050203_is_open U <-> q1050203_is_open V);
  q1050203_open_univ :
    q1050203_is_open (fun _ : X => True);
  q1050203_open_inter :
    forall U V : q1050203_set X,
      q1050203_is_open U ->
      q1050203_is_open V ->
      q1050203_is_open (fun x : X => U x /\ V x);
  q1050203_open_sUnion :
    forall family : q1050203_family X,
      (forall U : q1050203_set X,
        q1050203_member family U -> q1050203_is_open U) ->
      q1050203_is_open
        (fun x : X =>
          exists U : q1050203_set X,
            q1050203_member family U /\ U x)
}.

Arguments q1050203_is_open {X} _ _.

Definition q1050203_is_closed
    {X : Type}
    (T : q1050203_topological_space X)
    (U : q1050203_set X) : Prop :=
  q1050203_is_open T (fun x : X => ~ U x).

Definition q1050203_is_compact
    {X : Type}
    (T : q1050203_topological_space X)
    (U : q1050203_set X) : Prop :=
  forall cover : q1050203_family X,
    (forall V : q1050203_set X,
      q1050203_member cover V -> q1050203_is_open T V) ->
    (forall x : X,
      U x ->
      exists V : q1050203_set X,
        q1050203_member cover V /\ V x) ->
    exists finite_cover : list (q1050203_set X),
      Forall (fun V => q1050203_member cover V) finite_cover /\
      forall x : X,
        U x ->
        exists V : q1050203_set X,
          In V finite_cover /\ V x.

Definition q1050203_nonempty_set
    {X : Type} (U : q1050203_set X) : Prop :=
  exists x : X, U x.

Definition q1050203_nonempty_family
    {X : Type}
    (S : q1050203_family X) : Prop :=
  exists U : q1050203_set X, q1050203_member S U.

Definition q1050203_directed_on_reverse_inclusion
    {X : Type}
    (S : q1050203_family X) : Prop :=
  forall U V : q1050203_set X,
    q1050203_member S U ->
    q1050203_member S V ->
    exists W : q1050203_set X,
      q1050203_member S W /\
      (forall x : X, W x -> U x) /\
      (forall x : X, W x -> V x).

Definition q1050203_sInter
    {X : Type}
    (S : q1050203_family X) : q1050203_set X :=
  fun x : X =>
    forall U : q1050203_set X,
      q1050203_member S U -> U x.

Theorem nonempty_sInter_of_directed_nonempty_isCompact_isClosed :
  forall (X : Type)
         (T : q1050203_topological_space X)
         (S : q1050203_family X),
    q1050203_nonempty_family S ->
    q1050203_directed_on_reverse_inclusion S ->
    (forall U : q1050203_set X,
      q1050203_member S U -> q1050203_nonempty_set U) ->
    (forall U : q1050203_set X,
      q1050203_member S U -> q1050203_is_compact T U) ->
    (forall U : q1050203_set X,
      q1050203_member S U -> q1050203_is_closed T U) ->
    q1050203_nonempty_set (q1050203_sInter S).
Admitted.
