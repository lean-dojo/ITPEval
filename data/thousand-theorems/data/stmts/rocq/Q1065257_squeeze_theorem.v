(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1065257
  (thousand-theorems__rocq__Q1065257), "Squeeze theorem": for functions into
  a preordered space with its order topology, if lower and upper functions
  converge to the same limit and eventually bound a middle function, then the
  middle function converges to that limit. This file contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q1065257_set (X : Type) : Type := X -> Prop.

Definition q1065257_subset
    {X : Type}
    (U V : q1065257_set X) : Prop :=
  forall x : X, U x -> V x.

Record q1065257_preorder (X : Type) : Type := {
  q1065257_le : X -> X -> Prop;
  q1065257_le_refl :
    forall x : X, q1065257_le x x;
  q1065257_le_trans :
    forall x y z : X,
      q1065257_le x y ->
      q1065257_le y z ->
      q1065257_le x z
}.

Arguments q1065257_le {X} _ _ _.

Definition q1065257_lt
    {X : Type}
    (O : q1065257_preorder X)
    (x y : X) : Prop :=
  q1065257_le O x y /\ ~ q1065257_le O y x.

Record q1065257_topological_space (X : Type) : Type := {
  q1065257_is_open : q1065257_set X -> Prop;
  q1065257_open_univ :
    q1065257_is_open (fun _ : X => True);
  q1065257_open_inter :
    forall U V : q1065257_set X,
      q1065257_is_open U ->
      q1065257_is_open V ->
      q1065257_is_open (fun x : X => U x /\ V x);
  q1065257_open_sUnion :
    forall family : q1065257_set (q1065257_set X),
      (forall U : q1065257_set X,
        family U -> q1065257_is_open U) ->
      q1065257_is_open
        (fun x : X =>
          exists U : q1065257_set X, family U /\ U x)
}.

Arguments q1065257_is_open {X} _ _.

Definition q1065257_generated_order_open
    {X : Type}
    (O : q1065257_preorder X)
    (U : q1065257_set X) : Prop :=
  forall T : q1065257_topological_space X,
    (forall a : X,
      q1065257_is_open T
        (fun x : X => q1065257_lt O a x)) ->
    (forall a : X,
      q1065257_is_open T
        (fun x : X => q1065257_lt O x a)) ->
    q1065257_is_open T U.

Definition q1065257_order_topology
    {X : Type}
    (O : q1065257_preorder X)
    (T : q1065257_topological_space X) : Prop :=
  forall U : q1065257_set X,
    q1065257_is_open T U <->
    q1065257_generated_order_open O U.

Record q1065257_filter (X : Type) : Type := {
  q1065257_filter_sets : q1065257_set X -> Prop;
  q1065257_filter_univ :
    q1065257_filter_sets (fun _ : X => True);
  q1065257_filter_superset :
    forall U V : q1065257_set X,
      q1065257_filter_sets U ->
      q1065257_subset U V ->
      q1065257_filter_sets V;
  q1065257_filter_inter :
    forall U V : q1065257_set X,
      q1065257_filter_sets U ->
      q1065257_filter_sets V ->
      q1065257_filter_sets (fun x : X => U x /\ V x)
}.

Arguments q1065257_filter_sets {X} _ _.

Definition q1065257_eventually
    {X : Type}
    (F : q1065257_filter X)
    (P : X -> Prop) : Prop :=
  q1065257_filter_sets F P.

Definition q1065257_neighborhood
    {X : Type}
    (T : q1065257_topological_space X)
    (a : X)
    (U : q1065257_set X) : Prop :=
  exists V : q1065257_set X,
    q1065257_is_open T V /\
    V a /\
    q1065257_subset V U.

Definition q1065257_tendsto
    {X Y : Type}
    (f : X -> Y)
    (F : q1065257_filter X)
    (T : q1065257_topological_space Y)
    (a : Y) : Prop :=
  forall U : q1065257_set Y,
    q1065257_neighborhood T a U ->
    q1065257_eventually F (fun x : X => U (f x)).

Theorem tendsto_of_tendsto_of_tendsto_of_le_of_le' :
  forall (Alpha Beta : Type)
         (O : q1065257_preorder Alpha)
         (T : q1065257_topological_space Alpha)
         (F : q1065257_filter Beta)
         (f g h : Beta -> Alpha)
         (a : Alpha),
    q1065257_order_topology O T ->
    q1065257_tendsto g F T a ->
    q1065257_tendsto h F T a ->
    q1065257_eventually F
      (fun x : Beta => q1065257_le O (g x) (f x)) ->
    q1065257_eventually F
      (fun x : Beta => q1065257_le O (f x) (h x)) ->
    q1065257_tendsto f F T a.
Admitted.
