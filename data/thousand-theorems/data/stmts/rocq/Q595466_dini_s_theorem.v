(*
  Statement-only formalization of Thousand Theorems corpus artifact Q595466
  (thousand-theorems__rocq__Q595466), "Dini's theorem": a monotone increasing
  family of continuous functions, indexed by an arbitrary preorder and taking
  values in a normed lattice ordered additive commutative group with solid
  norm, converges locally uniformly when it converges pointwise to a
  continuous function. This file contains no proof.
*)

From Stdlib Require Import List Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q595466_set (A : Type) : Type := A -> Prop.

Definition q595466_subset {A : Type}
    (U V : q595466_set A) : Prop :=
  forall x : A, U x -> V x.

Record q595466_preorder (I : Type) : Type := {
  q595466_index_le : I -> I -> Prop;
  q595466_index_le_refl :
    forall i : I, q595466_index_le i i;
  q595466_index_le_trans :
    forall i j k : I,
      q595466_index_le i j ->
      q595466_index_le j k ->
      q595466_index_le i k
}.

Arguments q595466_index_le {I} _ _ _.

Record q595466_topological_space (X : Type) : Type := {
  q595466_is_open : q595466_set X -> Prop;
  q595466_open_ext :
    forall U V : q595466_set X,
      (forall x : X, U x <-> V x) ->
      (q595466_is_open U <-> q595466_is_open V);
  q595466_open_univ :
    q595466_is_open (fun _ : X => True);
  q595466_open_inter :
    forall U V : q595466_set X,
      q595466_is_open U ->
      q595466_is_open V ->
      q595466_is_open (fun x : X => U x /\ V x);
  q595466_open_sUnion :
    forall family : q595466_set (q595466_set X),
      (forall U : q595466_set X,
        family U -> q595466_is_open U) ->
      q595466_is_open
        (fun x : X =>
          exists U : q595466_set X, family U /\ U x)
}.

Arguments q595466_is_open {X} _ _.

Definition q595466_neighborhood {X : Type}
    (T : q595466_topological_space X)
    (x : X)
    (U : q595466_set X) : Prop :=
  exists V : q595466_set X,
    q595466_is_open T V /\
    V x /\
    q595466_subset V U.

Record q595466_normed_add_comm_group (G : Type) : Type := {
  q595466_zero : G;
  q595466_add : G -> G -> G;
  q595466_neg : G -> G;
  q595466_norm : G -> R;
  q595466_add_assoc :
    forall x y z : G,
      q595466_add x (q595466_add y z) =
      q595466_add (q595466_add x y) z;
  q595466_add_comm :
    forall x y : G,
      q595466_add x y = q595466_add y x;
  q595466_add_zero :
    forall x : G,
      q595466_add x q595466_zero = x;
  q595466_add_neg :
    forall x : G,
      q595466_add x (q595466_neg x) = q595466_zero;
  q595466_norm_nonnegative :
    forall x : G, 0 <= q595466_norm x;
  q595466_norm_eq_zero :
    forall x : G,
      q595466_norm x = 0 <-> x = q595466_zero;
  q595466_norm_neg :
    forall x : G,
      q595466_norm (q595466_neg x) = q595466_norm x;
  q595466_norm_add_le :
    forall x y : G,
      q595466_norm (q595466_add x y) <=
      q595466_norm x + q595466_norm y
}.

Arguments q595466_zero {G} _.
Arguments q595466_add {G} _ _ _.
Arguments q595466_neg {G} _ _.
Arguments q595466_norm {G} _ _.

Record q595466_lattice (G : Type) : Type := {
  q595466_le : G -> G -> Prop;
  q595466_inf : G -> G -> G;
  q595466_sup : G -> G -> G;
  q595466_le_refl :
    forall x : G, q595466_le x x;
  q595466_le_antisym :
    forall x y : G,
      q595466_le x y ->
      q595466_le y x ->
      x = y;
  q595466_le_trans :
    forall x y z : G,
      q595466_le x y ->
      q595466_le y z ->
      q595466_le x z;
  q595466_inf_le_left :
    forall x y : G,
      q595466_le (q595466_inf x y) x;
  q595466_inf_le_right :
    forall x y : G,
      q595466_le (q595466_inf x y) y;
  q595466_le_inf :
    forall x y z : G,
      q595466_le x y ->
      q595466_le x z ->
      q595466_le x (q595466_inf y z);
  q595466_le_sup_left :
    forall x y : G,
      q595466_le x (q595466_sup x y);
  q595466_le_sup_right :
    forall x y : G,
      q595466_le y (q595466_sup x y);
  q595466_sup_le :
    forall x y z : G,
      q595466_le x z ->
      q595466_le y z ->
      q595466_le (q595466_sup x y) z
}.

Arguments q595466_le {G} _ _ _.
Arguments q595466_inf {G} _ _ _.
Arguments q595466_sup {G} _ _ _.

Definition q595466_is_ordered_add_monoid {G : Type}
    (V : q595466_normed_add_comm_group G)
    (L : q595466_lattice G) : Prop :=
  forall a b : G,
    q595466_le L a b ->
    forall c : G,
      q595466_le L
        (q595466_add V c a)
        (q595466_add V c b).

Definition q595466_abs {G : Type}
    (V : q595466_normed_add_comm_group G)
    (L : q595466_lattice G)
    (x : G) : G :=
  q595466_sup L x (q595466_neg V x).

Definition q595466_has_solid_norm {G : Type}
    (V : q595466_normed_add_comm_group G)
    (L : q595466_lattice G) : Prop :=
  forall x y : G,
    q595466_le L
      (q595466_abs V L x)
      (q595466_abs V L y) ->
    q595466_norm V x <= q595466_norm V y.

Definition q595466_sub {G : Type}
    (V : q595466_normed_add_comm_group G)
    (x y : G) : G :=
  q595466_add V x (q595466_neg V y).

Definition q595466_dist {G : Type}
    (V : q595466_normed_add_comm_group G)
    (x y : G) : R :=
  q595466_norm V (q595466_sub V x y).

Definition q595466_metric_is_open {G : Type}
    (V : q595466_normed_add_comm_group G)
    (U : q595466_set G) : Prop :=
  forall x : G,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : G,
        q595466_dist V x y < epsilon ->
        U y.

Definition q595466_continuous {X G : Type}
    (T : q595466_topological_space X)
    (V : q595466_normed_add_comm_group G)
    (f : X -> G) : Prop :=
  forall U : q595466_set G,
    q595466_metric_is_open V U ->
    q595466_is_open T (fun x : X => U (f x)).

Definition q595466_eventually_at_top {I : Type}
    (O : q595466_preorder I)
    (P : I -> Prop) : Prop :=
  exists bounds : list I,
    forall i : I,
      (forall b : I,
        In b bounds ->
        q595466_index_le O b i) ->
      P i.

Definition q595466_pointwise_tendsto {I X G : Type}
    (O : q595466_preorder I)
    (V : q595466_normed_add_comm_group G)
    (F : I -> X -> G)
    (f : X -> G) : Prop :=
  forall (x : X) (epsilon : R),
    0 < epsilon ->
    q595466_eventually_at_top O
      (fun i : I =>
        q595466_dist V (F i x) (f x) < epsilon).

Definition q595466_monotone {I X G : Type}
    (O : q595466_preorder I)
    (L : q595466_lattice G)
    (F : I -> X -> G) : Prop :=
  forall i j : I,
    q595466_index_le O i j ->
    forall x : X,
      q595466_le L (F i x) (F j x).

Definition q595466_tendsto_locally_uniformly {I X G : Type}
    (O : q595466_preorder I)
    (T : q595466_topological_space X)
    (V : q595466_normed_add_comm_group G)
    (F : I -> X -> G)
    (f : X -> G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    forall x : X,
      exists U : q595466_set X,
        q595466_neighborhood T x U /\
        q595466_eventually_at_top O
          (fun i : I =>
            forall y : X,
              U y ->
              q595466_dist V (F i y) (f y) < epsilon).

Theorem Monotone_tendstoLocallyUniformly_of_forall_tendsto :
  forall (I X G : Type)
         (O : q595466_preorder I)
         (T : q595466_topological_space X)
         (V : q595466_normed_add_comm_group G)
         (L : q595466_lattice G)
         (F : I -> X -> G)
         (f : X -> G),
    q595466_has_solid_norm V L ->
    q595466_is_ordered_add_monoid V L ->
    (forall i : I, q595466_continuous T V (F i)) ->
    q595466_monotone O L F ->
    q595466_continuous T V f ->
    q595466_pointwise_tendsto O V F f ->
    q595466_tendsto_locally_uniformly O T V F f.
Admitted.
