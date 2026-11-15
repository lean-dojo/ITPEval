(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1477053
  (thousand-theorems__rocq__Q1477053), "Arzelà–Ascoli theorem": on a compact
  topological space, a pointwise equicontinuous family of bounded continuous
  functions with values in a fixed compact subset of a Hausdorff pseudometric
  space has compact closure in the uniform-convergence topology. This file
  contains no proof.
*)

From Stdlib Require Import List Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1477053_set (A : Type) : Type := A -> Prop.

Record q1477053_topological_space (X : Type) : Type := {
  q1477053_is_open : q1477053_set X -> Prop;
  q1477053_open_ext :
    forall U V : q1477053_set X,
      (forall x : X, U x <-> V x) ->
      (q1477053_is_open U <-> q1477053_is_open V);
  q1477053_open_univ :
    q1477053_is_open (fun _ : X => True);
  q1477053_open_inter :
    forall U V : q1477053_set X,
      q1477053_is_open U ->
      q1477053_is_open V ->
      q1477053_is_open (fun x : X => U x /\ V x);
  q1477053_open_sUnion :
    forall family : q1477053_set (q1477053_set X),
      (forall U : q1477053_set X,
        family U -> q1477053_is_open U) ->
      q1477053_is_open
        (fun x : X =>
          exists U : q1477053_set X, family U /\ U x)
}.

Arguments q1477053_is_open {X} _ _.

Record q1477053_pseudo_metric_space (Y : Type) : Type := {
  q1477053_dist : Y -> Y -> R;
  q1477053_dist_nonnegative :
    forall x y : Y, 0 <= q1477053_dist x y;
  q1477053_dist_self :
    forall x : Y, q1477053_dist x x = 0;
  q1477053_dist_symmetric :
    forall x y : Y, q1477053_dist x y = q1477053_dist y x;
  q1477053_dist_triangle :
    forall x y z : Y,
      q1477053_dist x z <=
      q1477053_dist x y + q1477053_dist y z
}.

Arguments q1477053_dist {Y} _ _ _.

Definition q1477053_t2_space
    {Y : Type}
    (M : q1477053_pseudo_metric_space Y) : Prop :=
  forall x y : Y,
    q1477053_dist M x y = 0 ->
    x = y.

Definition q1477053_metric_is_open
    {Y : Type}
    (M : q1477053_pseudo_metric_space Y)
    (U : q1477053_set Y) : Prop :=
  forall x : Y,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : Y,
        q1477053_dist M x y < epsilon ->
        U y.

Definition q1477053_is_compact
    {X : Type}
    (is_open : q1477053_set (q1477053_set X))
    (K : q1477053_set X) : Prop :=
  forall cover : q1477053_set (q1477053_set X),
    (forall U : q1477053_set X,
      cover U -> is_open U) ->
    (forall x : X,
      K x ->
      exists U : q1477053_set X, cover U /\ U x) ->
    exists finite_cover : list (q1477053_set X),
      Forall cover finite_cover /\
      forall x : X,
        K x ->
        exists U : q1477053_set X,
          In U finite_cover /\ U x.

Definition q1477053_compact_space
    {X : Type}
    (T : q1477053_topological_space X) : Prop :=
  q1477053_is_compact
    (q1477053_is_open T)
    (fun _ : X => True).

Definition q1477053_compact_metric_set
    {Y : Type}
    (M : q1477053_pseudo_metric_space Y)
    (K : q1477053_set Y) : Prop :=
  q1477053_is_compact (q1477053_metric_is_open M) K.

Definition q1477053_continuous
    {X Y : Type}
    (T : q1477053_topological_space X)
    (M : q1477053_pseudo_metric_space Y)
    (f : X -> Y) : Prop :=
  forall V : q1477053_set Y,
    q1477053_metric_is_open M V ->
    q1477053_is_open T (fun x : X => V (f x)).

Definition q1477053_bounded_range
    {X Y : Type}
    (M : q1477053_pseudo_metric_space Y)
    (f : X -> Y) : Prop :=
  exists bound : R,
    0 <= bound /\
    forall x y : X,
      q1477053_dist M (f x) (f y) <= bound.

Definition q1477053_bounded_continuous
    {X Y : Type}
    (T : q1477053_topological_space X)
    (M : q1477053_pseudo_metric_space Y)
    (f : X -> Y) : Prop :=
  q1477053_continuous T M f /\
  q1477053_bounded_range M f.

Definition q1477053_uniform_is_open
    {X Y : Type}
    (T : q1477053_topological_space X)
    (M : q1477053_pseudo_metric_space Y)
    (U : q1477053_set (X -> Y)) : Prop :=
  forall f : X -> Y,
    q1477053_bounded_continuous T M f ->
    U f ->
    exists epsilon : R,
      0 < epsilon /\
      forall g : X -> Y,
        q1477053_bounded_continuous T M g ->
        (forall x : X,
          q1477053_dist M (f x) (g x) < epsilon) ->
        U g.

Definition q1477053_uniform_is_closed
    {X Y : Type}
    (T : q1477053_topological_space X)
    (M : q1477053_pseudo_metric_space Y)
    (C : q1477053_set (X -> Y)) : Prop :=
  q1477053_uniform_is_open T M
    (fun f : X -> Y =>
      q1477053_bounded_continuous T M f /\ ~ C f).

Definition q1477053_uniform_closure
    {X Y : Type}
    (T : q1477053_topological_space X)
    (M : q1477053_pseudo_metric_space Y)
    (A : q1477053_set (X -> Y)) :
    q1477053_set (X -> Y) :=
  fun f : X -> Y =>
    q1477053_bounded_continuous T M f /\
    forall C : q1477053_set (X -> Y),
      q1477053_uniform_is_closed T M C ->
      (forall g : X -> Y,
        q1477053_bounded_continuous T M g ->
        A g ->
        C g) ->
      C f.

Definition q1477053_equicontinuous
    {X Y : Type}
    (T : q1477053_topological_space X)
    (M : q1477053_pseudo_metric_space Y)
    (A : q1477053_set (X -> Y)) : Prop :=
  forall (x : X) (epsilon : R),
    0 < epsilon ->
    exists U : q1477053_set X,
      q1477053_is_open T U /\
      U x /\
      forall (f : X -> Y) (y z : X),
        A f ->
        U y ->
        U z ->
        q1477053_dist M (f y) (f z) < epsilon.

Theorem q1477053_arzela_ascoli :
  forall (X Y : Type)
         (T : q1477053_topological_space X)
         (M : q1477053_pseudo_metric_space Y)
         (s : q1477053_set Y)
         (A : q1477053_set (X -> Y)),
    q1477053_compact_space T ->
    q1477053_t2_space M ->
    q1477053_compact_metric_set M s ->
    (forall f : X -> Y,
      A f ->
      q1477053_bounded_continuous T M f) ->
    (forall (f : X -> Y) (x : X),
      A f ->
      s (f x)) ->
    q1477053_equicontinuous T M A ->
    q1477053_is_compact
      (q1477053_uniform_is_open T M)
      (q1477053_uniform_closure T M A).
Admitted.
