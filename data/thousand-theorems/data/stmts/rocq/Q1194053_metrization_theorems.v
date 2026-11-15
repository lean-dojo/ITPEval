(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1194053
  (thousand-theorems__rocq__Q1194053), "Metrization theorems": every T3
  topological space with a second-countable topology admits a metric inducing
  exactly that topology. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1194053_set (A : Type) : Type := A -> Prop.

Record q1194053_topological_space (X : Type) : Type := {
  q1194053_is_open : q1194053_set X -> Prop;
  q1194053_open_ext :
    forall U V : q1194053_set X,
      (forall x : X, U x <-> V x) ->
      (q1194053_is_open U <-> q1194053_is_open V);
  q1194053_open_univ :
    q1194053_is_open (fun _ : X => True);
  q1194053_open_inter :
    forall U V : q1194053_set X,
      q1194053_is_open U ->
      q1194053_is_open V ->
      q1194053_is_open (fun x : X => U x /\ V x);
  q1194053_open_sUnion :
    forall family : q1194053_set (q1194053_set X),
      (forall U : q1194053_set X,
        family U -> q1194053_is_open U) ->
      q1194053_is_open
        (fun x : X =>
          exists U : q1194053_set X, family U /\ U x)
}.

Arguments q1194053_is_open {X} _ _.

Definition q1194053_is_closed
    {X : Type}
    (T : q1194053_topological_space X)
    (C : q1194053_set X) : Prop :=
  q1194053_is_open T (fun x : X => ~ C x).

Record q1194053_t3_space
    {X : Type}
    (T : q1194053_topological_space X) : Prop := {
  q1194053_t0 :
    forall x y : X,
      (forall U : q1194053_set X,
        q1194053_is_open T U -> (U x <-> U y)) ->
      x = y;
  q1194053_regular :
    forall (C : q1194053_set X) (x : X),
      q1194053_is_closed T C ->
      ~ C x ->
      exists U V : q1194053_set X,
        q1194053_is_open T U /\
        q1194053_is_open T V /\
        U x /\
        (forall y : X, C y -> V y) /\
        (forall y : X, ~ (U y /\ V y))
}.

Definition q1194053_second_countable
    {X : Type}
    (T : q1194053_topological_space X) : Prop :=
  exists basis : nat -> q1194053_set X,
    (forall n : nat, q1194053_is_open T (basis n)) /\
    forall (U : q1194053_set X) (x : X),
      q1194053_is_open T U ->
      U x ->
      exists n : nat,
        basis n x /\
        forall y : X, basis n y -> U y.

Record q1194053_metric_space (X : Type) : Type := {
  q1194053_dist : X -> X -> R;
  q1194053_dist_nonnegative :
    forall x y : X, 0 <= q1194053_dist x y;
  q1194053_dist_eq_zero :
    forall x y : X, q1194053_dist x y = 0 <-> x = y;
  q1194053_dist_symmetric :
    forall x y : X, q1194053_dist x y = q1194053_dist y x;
  q1194053_triangle :
    forall x y z : X,
      q1194053_dist x z <=
      q1194053_dist x y + q1194053_dist y z
}.

Arguments q1194053_dist {X} _ _ _.

Definition q1194053_metric_induces
    {X : Type}
    (T : q1194053_topological_space X)
    (M : q1194053_metric_space X) : Prop :=
  forall U : q1194053_set X,
    q1194053_is_open T U <->
    forall x : X, U x ->
      exists epsilon : R,
        0 < epsilon /\
        forall y : X,
          q1194053_dist M x y < epsilon ->
          U y.

Theorem metrizableSpace_of_t3_secondCountable :
  forall (X : Type)
         (T : q1194053_topological_space X),
    q1194053_t3_space T ->
    q1194053_second_countable T ->
    exists M : q1194053_metric_space X,
      q1194053_metric_induces T M.
Admitted.
