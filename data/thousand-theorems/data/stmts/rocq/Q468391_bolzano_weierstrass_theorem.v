(*
  Statement-only formalization of Thousand Theorems corpus artifact Q468391
  (thousand-theorems__rocq__Q468391), "Bolzano-Weierstrass theorem": in a
  proper pseudometric space, a sequence that is frequently contained in a
  bounded set has a strictly monotone subsequence converging to a point in the
  closure of that set; this also applies when every term lies in the set.
  This file contains no proof.
*)

From Stdlib Require Import List Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q468391_set (A : Type) : Type := A -> Prop.

Record q468391_pseudo_metric_space (X : Type) : Type := {
  q468391_dist : X -> X -> R;
  q468391_dist_nonnegative :
    forall x y : X, 0 <= q468391_dist x y;
  q468391_dist_self :
    forall x : X, q468391_dist x x = 0;
  q468391_dist_symmetric :
    forall x y : X,
      q468391_dist x y = q468391_dist y x;
  q468391_dist_triangle :
    forall x y z : X,
      q468391_dist x z <=
      q468391_dist x y + q468391_dist y z
}.

Arguments q468391_dist {X} _ _ _.

Definition q468391_is_open
    {X : Type}
    (M : q468391_pseudo_metric_space X)
    (U : q468391_set X) : Prop :=
  forall x : X,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : X,
        q468391_dist M x y < epsilon ->
        U y.

Definition q468391_is_closed
    {X : Type}
    (M : q468391_pseudo_metric_space X)
    (S : q468391_set X) : Prop :=
  q468391_is_open M (fun x : X => ~ S x).

Definition q468391_closure
    {X : Type}
    (M : q468391_pseudo_metric_space X)
    (S : q468391_set X) : q468391_set X :=
  fun x : X =>
    forall C : q468391_set X,
      q468391_is_closed M C ->
      (forall y : X, S y -> C y) ->
      C x.

Definition q468391_is_compact
    {X : Type}
    (M : q468391_pseudo_metric_space X)
    (S : q468391_set X) : Prop :=
  forall cover : q468391_set (q468391_set X),
    (forall U : q468391_set X,
      cover U -> q468391_is_open M U) ->
    (forall x : X,
      S x ->
      exists U : q468391_set X, cover U /\ U x) ->
    exists finite_cover : list (q468391_set X),
      Forall cover finite_cover /\
      forall x : X,
        S x ->
        exists U : q468391_set X,
          In U finite_cover /\ U x.

Definition q468391_closed_ball
    {X : Type}
    (M : q468391_pseudo_metric_space X)
    (center : X)
    (radius : R) : q468391_set X :=
  fun x : X => q468391_dist M x center <= radius.

Definition q468391_proper_space
    {X : Type}
    (M : q468391_pseudo_metric_space X) : Prop :=
  forall (center : X) (radius : R),
    q468391_is_compact M
      (q468391_closed_ball M center radius).

Definition q468391_is_bounded
    {X : Type}
    (M : q468391_pseudo_metric_space X)
    (S : q468391_set X) : Prop :=
  exists bound : R,
    forall x y : X,
      S x ->
      S y ->
      q468391_dist M x y <= bound.

Definition q468391_frequently_at_top
    (P : nat -> Prop) : Prop :=
  ~ exists N : nat,
      forall n : nat,
        (N <= n)%nat -> ~ P n.

Definition q468391_strict_mono
    (phi : nat -> nat) : Prop :=
  forall i j : nat,
    (i < j)%nat -> (phi i < phi j)%nat.

Definition q468391_tends_to
    {X : Type}
    (M : q468391_pseudo_metric_space X)
    (u : nat -> X)
    (a : X) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q468391_dist M (u n) a < epsilon.

Theorem tendsto_subseq_of_frequently_bounded :
  forall (X : Type)
         (M : q468391_pseudo_metric_space X),
    q468391_proper_space M ->
    forall (s : q468391_set X) (x : nat -> X),
      q468391_is_bounded M s ->
      q468391_frequently_at_top (fun n : nat => s (x n)) ->
      exists a : X,
        q468391_closure M s a /\
        exists phi : nat -> nat,
          q468391_strict_mono phi /\
          q468391_tends_to M (fun n : nat => x (phi n)) a.
Admitted.

Theorem tendsto_subseq_of_bounded :
  forall (X : Type)
         (M : q468391_pseudo_metric_space X),
    q468391_proper_space M ->
    forall (s : q468391_set X) (x : nat -> X),
      q468391_is_bounded M s ->
      (forall n : nat, s (x n)) ->
      exists a : X,
        q468391_closure M s a /\
        exists phi : nat -> nat,
          q468391_strict_mono phi /\
          q468391_tends_to M (fun n : nat => x (phi n)) a.
Admitted.
