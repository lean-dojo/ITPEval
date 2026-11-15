(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1052678
  (thousand-theorems__rocq__Q1052678), "Baire category theorem": in a Baire
  topological space, the intersection of any countable family of open dense
  subsets is dense. This file contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q1052678_set (A : Type) : Type := A -> Prop.

Record q1052678_topological_space (X : Type) : Type := {
  q1052678_is_open : q1052678_set X -> Prop;
  q1052678_open_ext :
    forall U V : q1052678_set X,
      (forall x : X, U x <-> V x) ->
      (q1052678_is_open U <-> q1052678_is_open V);
  q1052678_open_univ :
    q1052678_is_open (fun _ : X => True);
  q1052678_open_inter :
    forall U V : q1052678_set X,
      q1052678_is_open U ->
      q1052678_is_open V ->
      q1052678_is_open (fun x : X => U x /\ V x);
  q1052678_open_sUnion :
    forall family : q1052678_set (q1052678_set X),
      (forall U : q1052678_set X,
        family U -> q1052678_is_open U) ->
      q1052678_is_open
        (fun x : X =>
          exists U : q1052678_set X, family U /\ U x)
}.

Arguments q1052678_is_open {X} _ _.

Definition q1052678_is_closed
    {X : Type}
    (T : q1052678_topological_space X)
    (U : q1052678_set X) : Prop :=
  q1052678_is_open T (fun x : X => ~ U x).

Definition q1052678_closure
    {X : Type}
    (T : q1052678_topological_space X)
    (U : q1052678_set X) : q1052678_set X :=
  fun x : X =>
    forall C : q1052678_set X,
      q1052678_is_closed T C ->
      (forall y : X, U y -> C y) ->
      C x.

Definition q1052678_dense
    {X : Type}
    (T : q1052678_topological_space X)
    (U : q1052678_set X) : Prop :=
  forall x : X, q1052678_closure T U x.

Definition q1052678_countable
    {A : Type}
    (S : q1052678_set A) : Prop :=
  exists encode : A -> nat,
    forall x y : A,
      S x -> S y ->
      encode x = encode y ->
      x = y.

Definition q1052678_sInter
    {X : Type}
    (S : q1052678_set (q1052678_set X)) : q1052678_set X :=
  fun x : X =>
    forall U : q1052678_set X, S U -> U x.

Record q1052678_baire_space
    {X : Type}
    (T : q1052678_topological_space X) : Prop := {
  q1052678_baire_property :
    forall f : nat -> q1052678_set X,
      (forall n : nat, q1052678_is_open T (f n)) ->
      (forall n : nat, q1052678_dense T (f n)) ->
      q1052678_dense T
        (fun x : X => forall n : nat, f n x)
}.

Theorem dense_sInter_of_isOpen :
  forall (X : Type)
         (T : q1052678_topological_space X)
         (B : q1052678_baire_space T)
         (S : q1052678_set (q1052678_set X)),
    (forall U : q1052678_set X,
      S U -> q1052678_is_open T U) ->
    q1052678_countable S ->
    (forall U : q1052678_set X,
      S U -> q1052678_dense T U) ->
    q1052678_dense T (q1052678_sInter S).
Admitted.
