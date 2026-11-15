(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2525646
  (thousand-theorems__rocq__Q2525646), "Jordan-Hölder theorem": two finite
  composition series in a Jordan-Hölder lattice with the same least and
  greatest elements have equivalent successive factors. This file contains
  no proof.
*)

From Stdlib Require Import Vectors.Fin.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q2525646_lattice (X : Type) : Type := {
  q2525646_le : X -> X -> Prop;
  q2525646_sup : X -> X -> X;
  q2525646_inf : X -> X -> X;
  q2525646_le_refl :
    forall x : X, q2525646_le x x;
  q2525646_le_trans :
    forall x y z : X,
      q2525646_le x y ->
      q2525646_le y z ->
      q2525646_le x z;
  q2525646_le_antisym :
    forall x y : X,
      q2525646_le x y ->
      q2525646_le y x ->
      x = y;
  q2525646_le_sup_left :
    forall x y : X,
      q2525646_le x (q2525646_sup x y);
  q2525646_le_sup_right :
    forall x y : X,
      q2525646_le y (q2525646_sup x y);
  q2525646_sup_least :
    forall x y z : X,
      q2525646_le x z ->
      q2525646_le y z ->
      q2525646_le (q2525646_sup x y) z;
  q2525646_inf_le_left :
    forall x y : X,
      q2525646_le (q2525646_inf x y) x;
  q2525646_inf_le_right :
    forall x y : X,
      q2525646_le (q2525646_inf x y) y;
  q2525646_inf_greatest :
    forall x y z : X,
      q2525646_le z x ->
      q2525646_le z y ->
      q2525646_le z (q2525646_inf x y)
}.

Arguments q2525646_le {X} _ _ _.
Arguments q2525646_sup {X} _ _ _.
Arguments q2525646_inf {X} _ _ _.

Definition q2525646_lt
    {X : Type}
    (L : q2525646_lattice X)
    (x y : X) : Prop :=
  q2525646_le L x y /\ ~ q2525646_le L y x.

Record q2525646_jordan_holder_lattice
    (X : Type)
    (L : q2525646_lattice X) : Type := {
  q2525646_is_maximal : X -> X -> Prop;
  q2525646_lt_of_is_maximal :
    forall x y : X,
      q2525646_is_maximal x y ->
      q2525646_lt L x y;
  q2525646_sup_eq_of_is_maximal :
    forall x y z : X,
      q2525646_is_maximal x z ->
      q2525646_is_maximal y z ->
      x <> y ->
      q2525646_sup L x y = z;
  q2525646_is_maximal_inf_left_of_is_maximal_sup :
    forall x y : X,
      q2525646_is_maximal x (q2525646_sup L x y) ->
      q2525646_is_maximal y (q2525646_sup L x y) ->
      q2525646_is_maximal (q2525646_inf L x y) x;
  q2525646_iso : (X * X)%type -> (X * X)%type -> Prop;
  q2525646_iso_symm :
    forall p q : (X * X)%type,
      q2525646_iso p q ->
      q2525646_iso q p;
  q2525646_iso_trans :
    forall p q r : (X * X)%type,
      q2525646_iso p q ->
      q2525646_iso q r ->
      q2525646_iso p r;
  q2525646_second_iso :
    forall x y : X,
      q2525646_is_maximal x (q2525646_sup L x y) ->
      q2525646_iso
        (x, q2525646_sup L x y)
        (q2525646_inf L x y, y)
}.

Arguments q2525646_is_maximal {X L} _ _ _.
Arguments q2525646_iso {X L} _ _ _.

Fixpoint q2525646_fin_cast_succ
    {n : nat} (i : Fin.t n) : Fin.t (S n) :=
  match i in Fin.t k return Fin.t (S k) with
  | @Fin.F1 k => @Fin.F1 (S k)
  | @Fin.FS k j => @Fin.FS (S k) (q2525646_fin_cast_succ j)
  end.

Fixpoint q2525646_fin_last (n : nat) : Fin.t (S n) :=
  match n with
  | 0 => Fin.F1
  | S k => Fin.FS (q2525646_fin_last k)
  end.

Record q2525646_composition_series
    (X : Type)
    (L : q2525646_lattice X)
    (J : @q2525646_jordan_holder_lattice X L) : Type := {
  q2525646_series_length : nat;
  q2525646_series_term :
    Fin.t (S q2525646_series_length) -> X;
  q2525646_series_step :
    forall i : Fin.t q2525646_series_length,
      q2525646_is_maximal J
        (q2525646_series_term (q2525646_fin_cast_succ i))
        (q2525646_series_term (Fin.FS i))
}.

Arguments q2525646_series_length {X L J} _.
Arguments q2525646_series_term {X L J} _ _.

Definition q2525646_series_head
    {X : Type}
    {L : q2525646_lattice X}
    {J : @q2525646_jordan_holder_lattice X L}
    (s : @q2525646_composition_series X L J) : X :=
  q2525646_series_term s Fin.F1.

Definition q2525646_series_last
    {X : Type}
    {L : q2525646_lattice X}
    {J : @q2525646_jordan_holder_lattice X L}
    (s : @q2525646_composition_series X L J) : X :=
  q2525646_series_term s
    (q2525646_fin_last (q2525646_series_length s)).

Record q2525646_bijection (A B : Type) : Type := {
  q2525646_bijection_forward : A -> B;
  q2525646_bijection_backward : B -> A;
  q2525646_bijection_left_inverse :
    forall x : A,
      q2525646_bijection_backward
        (q2525646_bijection_forward x) = x;
  q2525646_bijection_right_inverse :
    forall y : B,
      q2525646_bijection_forward
        (q2525646_bijection_backward y) = y
}.

Arguments q2525646_bijection_forward {A B} _ _.

Definition q2525646_series_equivalent
    {X : Type}
    {L : q2525646_lattice X}
    {J : @q2525646_jordan_holder_lattice X L}
    (s1 s2 : @q2525646_composition_series X L J) : Prop :=
  exists f :
      q2525646_bijection
        (Fin.t (q2525646_series_length s1))
        (Fin.t (q2525646_series_length s2)),
    forall i : Fin.t (q2525646_series_length s1),
      q2525646_iso J
        (q2525646_series_term s1 (q2525646_fin_cast_succ i),
         q2525646_series_term s1 (Fin.FS i))
        (q2525646_series_term s2
           (q2525646_fin_cast_succ
             (q2525646_bijection_forward f i)),
         q2525646_series_term s2
           (Fin.FS (q2525646_bijection_forward f i))).

Theorem CompositionSeries_jordan_holder :
  forall (X : Type)
         (L : q2525646_lattice X)
         (J : @q2525646_jordan_holder_lattice X L)
         (s1 s2 : @q2525646_composition_series X L J),
    q2525646_series_head s1 = q2525646_series_head s2 ->
    q2525646_series_last s1 = q2525646_series_last s2 ->
    q2525646_series_equivalent s1 s2.
Admitted.
