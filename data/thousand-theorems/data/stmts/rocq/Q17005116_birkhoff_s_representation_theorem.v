(*
  Statement-only formalization of Thousand Theorems corpus artifact Q17005116
  (thousand-theorems__rocq__Q17005116), "Birkhoff's representation theorem":
  the canonical map from a finite distributive lattice to sets of its
  sup-irreducible elements preserves joins and meets. This file contains no
  proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q17005116_distributive_lattice (A : Type) : Type := {
  q17005116_le : A -> A -> Prop;
  q17005116_join : A -> A -> A;
  q17005116_meet : A -> A -> A;
  q17005116_le_refl :
    forall x : A, q17005116_le x x;
  q17005116_le_trans :
    forall x y z : A,
      q17005116_le x y ->
      q17005116_le y z ->
      q17005116_le x z;
  q17005116_le_antisym :
    forall x y : A,
      q17005116_le x y ->
      q17005116_le y x ->
      x = y;
  q17005116_le_join_left :
    forall x y : A,
      q17005116_le x (q17005116_join x y);
  q17005116_le_join_right :
    forall x y : A,
      q17005116_le y (q17005116_join x y);
  q17005116_join_least :
    forall x y z : A,
      q17005116_le x z ->
      q17005116_le y z ->
      q17005116_le (q17005116_join x y) z;
  q17005116_meet_le_left :
    forall x y : A,
      q17005116_le (q17005116_meet x y) x;
  q17005116_meet_le_right :
    forall x y : A,
      q17005116_le (q17005116_meet x y) y;
  q17005116_meet_greatest :
    forall x y z : A,
      q17005116_le z x ->
      q17005116_le z y ->
      q17005116_le z (q17005116_meet x y);
  q17005116_meet_join_distrib_left :
    forall x y z : A,
      q17005116_meet x (q17005116_join y z) =
      q17005116_join
        (q17005116_meet x y) (q17005116_meet x z)
}.

Arguments q17005116_le {A} _ _ _.
Arguments q17005116_join {A} _ _ _.
Arguments q17005116_meet {A} _ _ _.

Record q17005116_finite_type (A : Type) : Type := {
  q17005116_enum : list A;
  q17005116_enum_nodup : NoDup q17005116_enum;
  q17005116_enum_complete :
    forall x : A, In x q17005116_enum
}.

Definition q17005116_is_bottom
    {A : Type}
    (L : q17005116_distributive_lattice A)
    (x : A) : Prop :=
  forall y : A, q17005116_le L x y.

Definition q17005116_sup_irreducible
    {A : Type}
    (L : q17005116_distributive_lattice A)
    (x : A) : Prop :=
  ~ q17005116_is_bottom L x /\
  forall y z : A,
    q17005116_join L y z = x ->
    y = x \/ z = x.

Definition q17005116_sup_irreducible_element
    {A : Type}
    (L : q17005116_distributive_lattice A) : Type :=
  {x : A | q17005116_sup_irreducible L x}.

Definition q17005116_set (X : Type) : Type :=
  X -> Prop.

Definition q17005116_set_equal
    {X : Type}
    (S T : q17005116_set X) : Prop :=
  forall x : X, S x <-> T x.

Definition q17005116_union
    {X : Type}
    (S T : q17005116_set X) : q17005116_set X :=
  fun x => S x \/ T x.

Definition q17005116_intersection
    {X : Type}
    (S T : q17005116_set X) : q17005116_set X :=
  fun x => S x /\ T x.

Definition q17005116_birkhoff_set
    {A : Type}
    (L : q17005116_distributive_lattice A)
    (a : A) :
    q17005116_set (q17005116_sup_irreducible_element L) :=
  fun p => q17005116_le L (proj1_sig p) a.

Definition q17005116_is_lattice_homomorphism
    {A X : Type}
    (L : q17005116_distributive_lattice A)
    (f : A -> q17005116_set X) : Prop :=
  (forall a b : A,
    q17005116_set_equal
      (f (q17005116_join L a b))
      (q17005116_union (f a) (f b))) /\
  forall a b : A,
    q17005116_set_equal
      (f (q17005116_meet L a b))
      (q17005116_intersection (f a) (f b)).

Theorem LatticeHom_birkhoffSet :
  forall (A : Type)
         (L : q17005116_distributive_lattice A)
         (_ : q17005116_finite_type A)
         (_ :
           forall x : A,
             {q17005116_sup_irreducible L x} +
             {~ q17005116_sup_irreducible L x}),
    @q17005116_is_lattice_homomorphism
      A (q17005116_sup_irreducible_element L) L
      (@q17005116_birkhoff_set A L) /\
    forall a b : A,
      q17005116_set_equal
        (@q17005116_birkhoff_set A L a)
        (@q17005116_birkhoff_set A L b) ->
      a = b.
Admitted.
