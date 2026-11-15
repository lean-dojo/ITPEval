(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1346677
  (thousand-theorems__rocq__Q1346677), "Tietze extension theorem": a bounded
  continuous real-valued function along a closed embedding into a normal
  topological space has a bounded continuous extension with the same norm.
  This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1346677_set (A : Type) : Type := A -> Prop.

Definition q1346677_subset {A : Type}
    (U V : q1346677_set A) : Prop :=
  forall x : A, U x -> V x.

Definition q1346677_disjoint {A : Type}
    (U V : q1346677_set A) : Prop :=
  forall x : A, ~ (U x /\ V x).

Definition q1346677_same_set {A : Type}
    (U V : q1346677_set A) : Prop :=
  forall x : A, U x <-> V x.

Record q1346677_topological_space (A : Type) : Type := {
  q1346677_is_open : q1346677_set A -> Prop;
  q1346677_open_extensional :
    forall U V : q1346677_set A,
      q1346677_same_set U V ->
      (q1346677_is_open U <-> q1346677_is_open V);
  q1346677_open_full :
    q1346677_is_open (fun _ : A => True);
  q1346677_open_intersection :
    forall U V : q1346677_set A,
      q1346677_is_open U ->
      q1346677_is_open V ->
      q1346677_is_open (fun x : A => U x /\ V x);
  q1346677_open_union :
    forall family : q1346677_set (q1346677_set A),
      (forall U : q1346677_set A,
        family U -> q1346677_is_open U) ->
      q1346677_is_open
        (fun x : A =>
          exists U : q1346677_set A, family U /\ U x)
}.

Arguments q1346677_is_open {A} _ _.

Definition q1346677_is_closed {A : Type}
    (T : q1346677_topological_space A)
    (C : q1346677_set A) : Prop :=
  q1346677_is_open T (fun x : A => ~ C x).

Definition q1346677_continuous {A B : Type}
    (TA : q1346677_topological_space A)
    (TB : q1346677_topological_space B)
    (f : A -> B) : Prop :=
  forall V : q1346677_set B,
    q1346677_is_open TB V ->
    q1346677_is_open TA (fun x : A => V (f x)).

Definition q1346677_normal_space {A : Type}
    (T : q1346677_topological_space A) : Prop :=
  forall C D : q1346677_set A,
    q1346677_is_closed T C ->
    q1346677_is_closed T D ->
    q1346677_disjoint C D ->
    exists U V : q1346677_set A,
      q1346677_is_open T U /\
      q1346677_is_open T V /\
      q1346677_subset C U /\
      q1346677_subset D V /\
      q1346677_disjoint U V.

Definition q1346677_range {A B : Type}
    (f : A -> B) : q1346677_set B :=
  fun y : B => exists x : A, f x = y.

Definition q1346677_closed_embedding {A B : Type}
    (TA : q1346677_topological_space A)
    (TB : q1346677_topological_space B)
    (e : A -> B) : Prop :=
  (forall x y : A, e x = e y -> x = y) /\
  q1346677_continuous TA TB e /\
  (forall U : q1346677_set A,
    q1346677_is_open TA U ->
    exists V : q1346677_set B,
      q1346677_is_open TB V /\
      forall x : A, U x <-> V (e x)) /\
  q1346677_is_closed TB (q1346677_range e).

Definition q1346677_real_open
    (U : q1346677_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Definition q1346677_continuous_real {A : Type}
    (T : q1346677_topological_space A)
    (f : A -> R) : Prop :=
  forall U : q1346677_set R,
    q1346677_real_open U ->
    q1346677_is_open T (fun x : A => U (f x)).

Record q1346677_bounded_continuous_real
    (A : Type) (T : q1346677_topological_space A) : Type := {
  q1346677_bc_apply : A -> R;
  q1346677_bc_continuous :
    q1346677_continuous_real T q1346677_bc_apply;
  q1346677_bc_norm : R;
  q1346677_bc_norm_nonnegative :
    0 <= q1346677_bc_norm;
  q1346677_bc_norm_upper_bound :
    forall x : A,
      Rabs (q1346677_bc_apply x) <= q1346677_bc_norm;
  q1346677_bc_norm_least :
    forall bound : R,
      0 <= bound ->
      (forall x : A, Rabs (q1346677_bc_apply x) <= bound) ->
      q1346677_bc_norm <= bound
}.

Arguments q1346677_bc_apply {A T} _ _.
Arguments q1346677_bc_norm {A T} _.

Theorem
BoundedContinuousFunction_exists_extension_norm_eq_of_isClosedEmbedding :
  forall (X Y : Type)
         (TX : q1346677_topological_space X)
         (TY : q1346677_topological_space Y)
         (f : q1346677_bounded_continuous_real TX)
         (e : X -> Y),
    q1346677_normal_space TY ->
    q1346677_closed_embedding TX TY e ->
    exists g : q1346677_bounded_continuous_real TY,
      q1346677_bc_norm g = q1346677_bc_norm f /\
      forall x : X,
        q1346677_bc_apply g (e x) =
        q1346677_bc_apply f x.
Admitted.
