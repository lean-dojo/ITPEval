(*
  Statement-only formalization of Thousand Theorems corpus artifact Q253214
  (thousand-theorems__rocq__Q253214), "Heine–Borel theorem": in a proper
  Hausdorff pseudometric space, a set is compact if and only if it is closed
  and bounded. This file contains no proof.
*)

From Stdlib Require Import List Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q253214_set (A : Type) : Type := A -> Prop.

Record q253214_pseudo_metric_space (X : Type) : Type := {
  q253214_dist : X -> X -> R;
  q253214_dist_nonnegative :
    forall x y : X, 0 <= q253214_dist x y;
  q253214_dist_self :
    forall x : X, q253214_dist x x = 0;
  q253214_dist_symmetric :
    forall x y : X,
      q253214_dist x y = q253214_dist y x;
  q253214_dist_triangle :
    forall x y z : X,
      q253214_dist x z <=
      q253214_dist x y + q253214_dist y z
}.

Arguments q253214_dist {X} _ _ _.

Definition q253214_is_open
    {X : Type}
    (M : q253214_pseudo_metric_space X)
    (U : q253214_set X) : Prop :=
  forall x : X,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : X,
        q253214_dist M x y < epsilon ->
        U y.

Definition q253214_is_closed
    {X : Type}
    (M : q253214_pseudo_metric_space X)
    (S : q253214_set X) : Prop :=
  q253214_is_open M (fun x : X => ~ S x).

Definition q253214_is_compact
    {X : Type}
    (M : q253214_pseudo_metric_space X)
    (S : q253214_set X) : Prop :=
  forall cover : q253214_set (q253214_set X),
    (forall U : q253214_set X,
      cover U -> q253214_is_open M U) ->
    (forall x : X,
      S x ->
      exists U : q253214_set X, cover U /\ U x) ->
    exists finite_cover : list (q253214_set X),
      Forall cover finite_cover /\
      forall x : X,
        S x ->
        exists U : q253214_set X,
          In U finite_cover /\ U x.

Definition q253214_is_bounded
    {X : Type}
    (M : q253214_pseudo_metric_space X)
    (S : q253214_set X) : Prop :=
  exists bound : R,
    forall x y : X,
      S x ->
      S y ->
      q253214_dist M x y <= bound.

Definition q253214_closed_ball
    {X : Type}
    (M : q253214_pseudo_metric_space X)
    (center : X)
    (radius : R) : q253214_set X :=
  fun x : X => q253214_dist M x center <= radius.

Definition q253214_t2_space
    {X : Type}
    (M : q253214_pseudo_metric_space X) : Prop :=
  forall x y : X,
    x <> y ->
    exists U V : q253214_set X,
      q253214_is_open M U /\
      q253214_is_open M V /\
      U x /\
      V y /\
      forall z : X, ~ (U z /\ V z).

Definition q253214_proper_space
    {X : Type}
    (M : q253214_pseudo_metric_space X) : Prop :=
  forall (center : X) (radius : R),
    q253214_is_compact M
      (q253214_closed_ball M center radius).

Theorem q253214_heine_borel_theorem :
  forall (X : Type)
         (M : q253214_pseudo_metric_space X),
    q253214_t2_space M ->
    q253214_proper_space M ->
    forall S : q253214_set X,
      q253214_is_compact M S <->
      q253214_is_closed M S /\
      q253214_is_bounded M S.
Admitted.
