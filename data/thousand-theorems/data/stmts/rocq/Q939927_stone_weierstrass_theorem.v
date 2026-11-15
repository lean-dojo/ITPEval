(*
  Statement-only formalization of Thousand Theorems corpus artifact Q939927
  (thousand-theorems__rocq__Q939927), "Stone–Weierstrass theorem": a real
  subalgebra of continuous functions on an arbitrary compact topological
  space that separates points is uniformly dense. This file contains no proof.
*)

From Stdlib Require Import Reals List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q939927_set (A : Type) : Type := A -> Prop.

Record q939927_topological_space (X : Type) : Type := {
  q939927_is_open : q939927_set X -> Prop;
  q939927_open_extensional :
    forall U V : q939927_set X,
      (forall x : X, U x <-> V x) ->
      (q939927_is_open U <-> q939927_is_open V);
  q939927_open_univ :
    q939927_is_open (fun _ : X => True);
  q939927_open_intersection :
    forall U V : q939927_set X,
      q939927_is_open U ->
      q939927_is_open V ->
      q939927_is_open (fun x : X => U x /\ V x);
  q939927_open_union :
    forall family : q939927_set (q939927_set X),
      (forall U : q939927_set X,
        family U -> q939927_is_open U) ->
      q939927_is_open
        (fun x : X =>
          exists U : q939927_set X, family U /\ U x)
}.

Arguments q939927_is_open {X} _ _.

Definition q939927_compact_space
    {X : Type} (T : q939927_topological_space X) : Prop :=
  forall cover : q939927_set (q939927_set X),
    (forall U : q939927_set X,
      cover U -> q939927_is_open T U) ->
    (forall x : X,
      exists U : q939927_set X, cover U /\ U x) ->
    exists finite_cover : list (q939927_set X),
      Forall cover finite_cover /\
      forall x : X,
        exists U : q939927_set X,
          In U finite_cover /\ U x.

Definition q939927_real_open
    (U : q939927_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Definition q939927_continuous_real
    {X : Type}
    (T : q939927_topological_space X)
    (f : X -> R) : Prop :=
  forall U : q939927_set R,
    q939927_real_open U ->
    q939927_is_open T (fun x : X => U (f x)).

Record q939927_real_subalgebra
    (X : Type) (T : q939927_topological_space X) : Type := {
  q939927_carrier : q939927_set (X -> R);
  q939927_carrier_continuous :
    forall f : X -> R,
      q939927_carrier f ->
      q939927_continuous_real T f;
  q939927_zero_mem :
    q939927_carrier (fun _ : X => 0);
  q939927_one_mem :
    q939927_carrier (fun _ : X => 1);
  q939927_add_mem :
    forall f g : X -> R,
      q939927_carrier f ->
      q939927_carrier g ->
      q939927_carrier (fun x : X => f x + g x);
  q939927_mul_mem :
    forall f g : X -> R,
      q939927_carrier f ->
      q939927_carrier g ->
      q939927_carrier (fun x : X => f x * g x);
  q939927_neg_mem :
    forall f : X -> R,
      q939927_carrier f ->
      q939927_carrier (fun x : X => - f x);
  q939927_smul_mem :
    forall (c : R) (f : X -> R),
      q939927_carrier f ->
      q939927_carrier (fun x : X => c * f x)
}.

Arguments q939927_real_subalgebra X T : clear implicits.
Arguments q939927_carrier {X T} _ _.

Definition q939927_separates_points
    {X : Type}
    {T : q939927_topological_space X}
    (A : q939927_real_subalgebra X T) : Prop :=
  forall x y : X,
    x <> y ->
    exists f : X -> R,
      q939927_carrier A f /\
      f x <> f y.

Theorem
ContinuousMap_subalgebra_topologicalClosure_eq_top_of_separatesPoints :
  forall (X : Type)
         (T : q939927_topological_space X)
         (A : q939927_real_subalgebra X T),
    q939927_compact_space T ->
    q939927_separates_points A ->
    forall f : X -> R,
      q939927_continuous_real T f ->
      forall epsilon : R,
        0 < epsilon ->
        exists g : X -> R,
          q939927_carrier A g /\
          forall x : X,
            Rabs (g x - f x) < epsilon.
Admitted.
