(*
  Statement-only formalization of Thousand Theorems corpus artifact Q765987
  (thousand-theorems__rocq__Q765987), "Heine–Cantor theorem": every
  continuous function from a compact uniform space to an arbitrary uniform
  space is uniformly continuous. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q765987_set (A : Type) : Type := A -> Prop.

Definition q765987_subset
    {A : Type}
    (U V : q765987_set A) : Prop :=
  forall x : A, U x -> V x.

Definition q765987_inverse
    {A : Type}
    (R : q765987_set (A * A)) : q765987_set (A * A) :=
  fun p : A * A => R (snd p, fst p).

Definition q765987_rel_comp
    {A : Type}
    (R S : q765987_set (A * A)) : q765987_set (A * A) :=
  fun p : A * A =>
    exists y : A, R (fst p, y) /\ S (y, snd p).

Record q765987_uniform_space (A : Type) : Type := {
  q765987_entourage : q765987_set (A * A) -> Prop;
  q765987_entourage_univ :
    q765987_entourage (fun _ : A * A => True);
  q765987_entourage_upward :
    forall U V : q765987_set (A * A),
      q765987_entourage U ->
      q765987_subset U V ->
      q765987_entourage V;
  q765987_entourage_inter :
    forall U V : q765987_set (A * A),
      q765987_entourage U ->
      q765987_entourage V ->
      q765987_entourage
        (fun p : A * A => U p /\ V p);
  q765987_entourage_diagonal :
    forall U : q765987_set (A * A),
      q765987_entourage U ->
      forall x : A, U (x, x);
  q765987_entourage_inverse :
    forall U : q765987_set (A * A),
      q765987_entourage U ->
      q765987_entourage (q765987_inverse U);
  q765987_entourage_square :
    forall U : q765987_set (A * A),
      q765987_entourage U ->
      exists V : q765987_set (A * A),
        q765987_entourage V /\
        q765987_subset (q765987_rel_comp V V) U
}.

Arguments q765987_entourage {A} _ _.

Definition q765987_is_open
    {A : Type}
    (U : q765987_uniform_space A)
    (O : q765987_set A) : Prop :=
  forall x : A,
    O x ->
    exists V : q765987_set (A * A),
      q765987_entourage U V /\
      forall y : A, V (x, y) -> O y.

Definition q765987_compact_space
    {A : Type}
    (U : q765987_uniform_space A) : Prop :=
  forall cover : q765987_set (q765987_set A),
    (forall O : q765987_set A,
      cover O -> q765987_is_open U O) ->
    (forall x : A,
      exists O : q765987_set A, cover O /\ O x) ->
    exists finite_cover : list (q765987_set A),
      Forall cover finite_cover /\
      forall x : A,
        exists O : q765987_set A,
          In O finite_cover /\ O x.

Definition q765987_continuous
    {A B : Type}
    (UA : q765987_uniform_space A)
    (UB : q765987_uniform_space B)
    (f : A -> B) : Prop :=
  forall O : q765987_set B,
    q765987_is_open UB O ->
    q765987_is_open UA (fun x : A => O (f x)).

Definition q765987_uniform_continuous
    {A B : Type}
    (UA : q765987_uniform_space A)
    (UB : q765987_uniform_space B)
    (f : A -> B) : Prop :=
  forall V : q765987_set (B * B),
    q765987_entourage UB V ->
    exists U : q765987_set (A * A),
      q765987_entourage UA U /\
      forall x y : A,
        U (x, y) -> V (f x, f y).

Theorem CompactSpace_uniformContinuous_of_continuous :
  forall (Alpha Beta : Type)
         (UA : q765987_uniform_space Alpha)
         (UB : q765987_uniform_space Beta)
         (f : Alpha -> Beta),
    q765987_compact_space UA ->
    q765987_continuous UA UB f ->
    q765987_uniform_continuous UA UB f.
Admitted.
