(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1137014
  (thousand-theorems__rocq__Q1137014), "Tychonoff's theorem": an arbitrary
  dependent product of compact subsets of topological spaces is compact in
  the finite-support product topology. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q1137014_set (A : Type) : Type := A -> Prop.

Definition q1137014_same_set
    {A : Type}
    (U V : q1137014_set A) : Prop :=
  forall x : A, U x <-> V x.

Record q1137014_family (A : Type) : Type := {
  q1137014_member : q1137014_set A -> Prop;
  q1137014_member_ext :
    forall U V : q1137014_set A,
      q1137014_same_set U V ->
      (q1137014_member U <-> q1137014_member V)
}.

Arguments q1137014_member {A} _ _.

Definition q1137014_finite
    {A : Type} (S : q1137014_set A) : Prop :=
  exists elements : list A,
    forall x : A, S x -> In x elements.

Record q1137014_topological_space (X : Type) : Type := {
  q1137014_is_open : q1137014_set X -> Prop;
  q1137014_open_ext :
    forall U V : q1137014_set X,
      q1137014_same_set U V ->
      (q1137014_is_open U <-> q1137014_is_open V);
  q1137014_open_univ :
    q1137014_is_open (fun _ : X => True);
  q1137014_open_inter :
    forall U V : q1137014_set X,
      q1137014_is_open U ->
      q1137014_is_open V ->
      q1137014_is_open (fun x : X => U x /\ V x);
  q1137014_open_sUnion :
    forall family : q1137014_family X,
      (forall U : q1137014_set X,
        q1137014_member family U -> q1137014_is_open U) ->
      q1137014_is_open
        (fun x : X =>
          exists U : q1137014_set X,
            q1137014_member family U /\ U x)
}.

Arguments q1137014_is_open {X} _ _.

Definition q1137014_is_compact
    {X : Type}
    (is_open : q1137014_set X -> Prop)
    (K : q1137014_set X) : Prop :=
  forall cover : q1137014_family X,
    (forall U : q1137014_set X,
      q1137014_member cover U -> is_open U) ->
    (forall x : X,
      K x ->
      exists U : q1137014_set X,
        q1137014_member cover U /\ U x) ->
    exists finite_cover : list (q1137014_set X),
      Forall (q1137014_member cover) finite_cover /\
      forall x : X,
        K x ->
        exists U : q1137014_set X,
          In U finite_cover /\ U x.

Definition q1137014_basic_product_open
    {I : Type}
    {X : I -> Type}
    (T : forall i : I, q1137014_topological_space (X i))
    (B : q1137014_set (forall i : I, X i)) : Prop :=
  exists U : forall i : I, q1137014_set (X i),
    (forall i : I, q1137014_is_open (T i) (U i)) /\
    (exists F : q1137014_set I,
      q1137014_finite F /\
      forall i : I,
        ~ F i ->
        forall x : X i, U i x) /\
    forall x : (forall i : I, X i),
      B x <-> forall i : I, U i (x i).

Definition q1137014_product_is_open
    {I : Type}
    {X : I -> Type}
    (T : forall i : I, q1137014_topological_space (X i))
    (V : q1137014_set (forall i : I, X i)) : Prop :=
  exists family : q1137014_family (forall i : I, X i),
    (forall B : q1137014_set (forall i : I, X i),
      q1137014_member family B ->
      q1137014_basic_product_open T B) /\
    forall x : (forall i : I, X i),
      V x <->
      exists B : q1137014_set (forall i : I, X i),
        q1137014_member family B /\ B x.

Theorem isCompact_pi_infinite :
  forall (I : Type)
         (X : I -> Type)
         (T : forall i : I, q1137014_topological_space (X i))
         (s : forall i : I, q1137014_set (X i)),
    (forall i : I,
      q1137014_is_compact
        (q1137014_is_open (T i))
        (s i)) ->
    q1137014_is_compact
      (q1137014_product_is_open T)
      (fun x : (forall i : I, X i) =>
        forall i : I, s i (x i)).
Admitted.
