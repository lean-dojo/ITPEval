(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1306095
  (thousand-theorems__rocq__Q1306095), "Whitney embedding theorem": every
  compact Hausdorff smooth finite-dimensional real manifold admits a smooth
  closed embedding into some finite-dimensional Euclidean space, with
  injective manifold derivative at every point. This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals List.

Import ListNotations.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1306095_set (A : Type) : Type := A -> Prop.

Record q1306095_normed_real_vector_space (E : Type) : Type := {
  q1306095_zero : E;
  q1306095_add : E -> E -> E;
  q1306095_neg : E -> E;
  q1306095_smul : R -> E -> E;
  q1306095_norm : E -> R;
  q1306095_add_assoc :
    forall x y z : E,
      q1306095_add x (q1306095_add y z) =
      q1306095_add (q1306095_add x y) z;
  q1306095_add_comm :
    forall x y : E, q1306095_add x y = q1306095_add y x;
  q1306095_add_zero :
    forall x : E, q1306095_add x q1306095_zero = x;
  q1306095_add_neg :
    forall x : E,
      q1306095_add x (q1306095_neg x) = q1306095_zero;
  q1306095_one_smul :
    forall x : E, q1306095_smul 1 x = x;
  q1306095_mul_smul :
    forall (a b : R) (x : E),
      q1306095_smul (a * b) x =
      q1306095_smul a (q1306095_smul b x);
  q1306095_add_smul :
    forall (a b : R) (x : E),
      q1306095_smul (a + b) x =
      q1306095_add
        (q1306095_smul a x) (q1306095_smul b x);
  q1306095_smul_add :
    forall (a : R) (x y : E),
      q1306095_smul a (q1306095_add x y) =
      q1306095_add
        (q1306095_smul a x) (q1306095_smul a y);
  q1306095_zero_smul :
    forall x : E, q1306095_smul 0 x = q1306095_zero;
  q1306095_smul_zero :
    forall a : R, q1306095_smul a q1306095_zero = q1306095_zero;
  q1306095_norm_nonnegative :
    forall x : E, 0 <= q1306095_norm x;
  q1306095_norm_eq_zero :
    forall x : E,
      q1306095_norm x = 0 <-> x = q1306095_zero;
  q1306095_norm_add_le :
    forall x y : E,
      q1306095_norm (q1306095_add x y) <=
      q1306095_norm x + q1306095_norm y;
  q1306095_norm_smul :
    forall (a : R) (x : E),
      q1306095_norm (q1306095_smul a x) =
      Rabs a * q1306095_norm x
}.

Arguments q1306095_zero {E} _.
Arguments q1306095_add {E} _ _ _.
Arguments q1306095_neg {E} _ _.
Arguments q1306095_smul {E} _ _ _.
Arguments q1306095_norm {E} _ _.

Definition q1306095_sub {E : Type}
    (V : q1306095_normed_real_vector_space E)
    (x y : E) : E :=
  q1306095_add V x (q1306095_neg V y).

Fixpoint q1306095_vector_sum
    {E : Type}
    (V : q1306095_normed_real_vector_space E)
    (n : nat) : (Fin.t n -> E) -> E :=
  match n as k return (Fin.t k -> E) -> E with
  | O => fun _ => q1306095_zero V
  | S k =>
      fun terms =>
        q1306095_add V
          (terms Fin.F1)
          (@q1306095_vector_sum E V k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q1306095_vector_sum {E} V n _.

Record q1306095_finite_dimensional
    {E : Type}
    (V : q1306095_normed_real_vector_space E) : Type := {
  q1306095_dimension : nat;
  q1306095_basis : Fin.t q1306095_dimension -> E;
  q1306095_basis_spans :
    forall x : E,
      exists coefficients : Fin.t q1306095_dimension -> R,
        x =
        q1306095_vector_sum V q1306095_dimension
          (fun i =>
            q1306095_smul V
              (coefficients i) (q1306095_basis i));
  q1306095_basis_independent :
    forall coefficients : Fin.t q1306095_dimension -> R,
      q1306095_vector_sum V q1306095_dimension
        (fun i =>
          q1306095_smul V
            (coefficients i) (q1306095_basis i)) =
      q1306095_zero V ->
      forall i : Fin.t q1306095_dimension,
        coefficients i = 0
}.

Record q1306095_topological_space (X : Type) : Type := {
  q1306095_is_open : q1306095_set X -> Prop;
  q1306095_open_ext :
    forall U V : q1306095_set X,
      (forall x : X, U x <-> V x) ->
      (q1306095_is_open U <-> q1306095_is_open V);
  q1306095_open_univ :
    q1306095_is_open (fun _ : X => True);
  q1306095_open_inter :
    forall U V : q1306095_set X,
      q1306095_is_open U ->
      q1306095_is_open V ->
      q1306095_is_open (fun x : X => U x /\ V x);
  q1306095_open_union :
    forall family : q1306095_set (q1306095_set X),
      (forall U : q1306095_set X,
        family U -> q1306095_is_open U) ->
      q1306095_is_open
        (fun x : X =>
          exists U : q1306095_set X, family U /\ U x)
}.

Arguments q1306095_is_open {X} _ _.

Definition q1306095_norm_open {E : Type}
    (V : q1306095_normed_real_vector_space E)
    (U : q1306095_set E) : Prop :=
  forall x : E,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : E,
        q1306095_norm V (q1306095_sub V y x) < radius ->
        U y.

Definition q1306095_continuous_on
    {X Y : Type}
    (TX : q1306095_topological_space X)
    (TY : q1306095_topological_space Y)
    (source : q1306095_set X)
    (f : X -> Y) : Prop :=
  forall V : q1306095_set Y,
    q1306095_is_open TY V ->
    exists U : q1306095_set X,
      q1306095_is_open TX U /\
      forall x : X, source x -> (V (f x) <-> U x).

Definition q1306095_continuous_norm_to_top
    {E Y : Type}
    (VE : q1306095_normed_real_vector_space E)
    (TY : q1306095_topological_space Y)
    (source : q1306095_set E)
    (f : E -> Y) : Prop :=
  forall V : q1306095_set Y,
    q1306095_is_open TY V ->
    exists U : q1306095_set E,
      q1306095_norm_open VE U /\
      forall x : E, source x -> (V (f x) <-> U x).

Definition q1306095_continuous_top_to_norm
    {X E : Type}
    (TX : q1306095_topological_space X)
    (VE : q1306095_normed_real_vector_space E)
    (source : q1306095_set X)
    (f : X -> E) : Prop :=
  forall V : q1306095_set E,
    q1306095_norm_open VE V ->
    exists U : q1306095_set X,
      q1306095_is_open TX U /\
      forall x : X, source x -> (V (f x) <-> U x).

Definition q1306095_hausdorff
    {X : Type}
    (T : q1306095_topological_space X) : Prop :=
  forall x y : X,
    x <> y ->
    exists U V : q1306095_set X,
      q1306095_is_open T U /\
      q1306095_is_open T V /\
      U x /\ V y /\
      forall z : X, ~ (U z /\ V z).

Definition q1306095_compact
    {X : Type}
    (T : q1306095_topological_space X) : Prop :=
  forall (J : Type) (U : J -> q1306095_set X),
    (forall j : J, q1306095_is_open T (U j)) ->
    (forall x : X, exists j : J, U j x) ->
    exists finite_subcover : list J,
      forall x : X,
        exists j : J, In j finite_subcover /\ U j x.

Record q1306095_continuous_linear_map
    {E F : Type}
    (VE : q1306095_normed_real_vector_space E)
    (VF : q1306095_normed_real_vector_space F) : Type := {
  q1306095_clm_fun : E -> F;
  q1306095_clm_add :
    forall x y : E,
      q1306095_clm_fun (q1306095_add VE x y) =
      q1306095_add VF
        (q1306095_clm_fun x) (q1306095_clm_fun y);
  q1306095_clm_smul :
    forall (a : R) (x : E),
      q1306095_clm_fun (q1306095_smul VE a x) =
      q1306095_smul VF a (q1306095_clm_fun x);
  q1306095_clm_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : E,
        q1306095_norm VF (q1306095_clm_fun x) <=
        bound * q1306095_norm VE x
}.

Arguments q1306095_clm_fun {E F VE VF} _ _.

Definition q1306095_has_frechet_derivative_within_at
    {E F : Type}
    (VE : q1306095_normed_real_vector_space E)
    (VF : q1306095_normed_real_vector_space F)
    (source : q1306095_set E)
    (f : E -> F)
    (x : E)
    (derivative : q1306095_continuous_linear_map VE VF) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : E,
        source y ->
        q1306095_norm VE (q1306095_sub VE y x) < delta ->
        q1306095_norm VF
          (q1306095_sub VF
            (q1306095_sub VF (f y) (f x))
            (q1306095_clm_fun derivative
              (q1306095_sub VE y x))) <=
        epsilon * q1306095_norm VE (q1306095_sub VE y x).

Definition q1306095_unique_diff_on
    {E : Type}
    (VE : q1306095_normed_real_vector_space E)
    (source : q1306095_set E) : Prop :=
  forall (x : E),
    source x ->
    forall (F : Type)
           (VF : q1306095_normed_real_vector_space F)
           (f : E -> F)
           (first second :
             q1306095_continuous_linear_map VE VF),
      @q1306095_has_frechet_derivative_within_at
        E F VE VF source f x first ->
      @q1306095_has_frechet_derivative_within_at
        E F VE VF source f x second ->
      forall v : E,
        q1306095_clm_fun first v =
        q1306095_clm_fun second v.

Definition q1306095_norm_interior
    {E : Type}
    (VE : q1306095_normed_real_vector_space E)
    (source : q1306095_set E) : q1306095_set E :=
  fun x : E =>
    exists radius : R,
      0 < radius /\
      forall y : E,
        q1306095_norm VE (q1306095_sub VE y x) < radius ->
        source y.

Definition q1306095_norm_closure
    {E : Type}
    (VE : q1306095_normed_real_vector_space E)
    (source : q1306095_set E) : q1306095_set E :=
  fun x : E =>
    forall radius : R,
      0 < radius ->
      exists y : E,
        source y /\
        q1306095_norm VE (q1306095_sub VE y x) < radius.

Record q1306095_model_with_corners
    {E H : Type}
    (VE : q1306095_normed_real_vector_space E)
    (TH : q1306095_topological_space H) : Type := {
  q1306095_model_source : q1306095_set E;
  q1306095_to_model : E -> H;
  q1306095_from_model : H -> E;
  q1306095_to_model_mem :
    forall x : E,
      q1306095_model_source x ->
      q1306095_from_model (q1306095_to_model x) = x;
  q1306095_from_model_mem :
    forall h : H,
      q1306095_model_source (q1306095_from_model h);
  q1306095_from_model_inverse :
    forall h : H,
      q1306095_to_model (q1306095_from_model h) = h;
  q1306095_to_model_continuous :
    q1306095_continuous_norm_to_top
      VE TH q1306095_model_source q1306095_to_model;
  q1306095_from_model_continuous :
    q1306095_continuous_top_to_norm
      TH VE (fun _ : H => True) q1306095_from_model;
  q1306095_model_source_convex :
    forall (x y : E) (t : R),
      q1306095_model_source x ->
      q1306095_model_source y ->
      0 <= t <= 1 ->
      q1306095_model_source
        (q1306095_add VE
          (q1306095_smul VE t x)
          (q1306095_smul VE (1 - t) y));
  q1306095_model_source_nonempty_interior :
    exists x : E,
      @q1306095_norm_interior E VE q1306095_model_source x;
  q1306095_model_source_unique_diff :
    @q1306095_unique_diff_on E VE q1306095_model_source;
  q1306095_model_source_dense_interior :
    forall x : E,
      q1306095_model_source x ->
      @q1306095_norm_closure E VE
        (@q1306095_norm_interior E VE q1306095_model_source) x;
  q1306095_model_source_contains_closure_interior :
    forall x : E,
      @q1306095_norm_closure E VE
        (@q1306095_norm_interior E VE q1306095_model_source) x ->
      q1306095_model_source x
}.

Arguments q1306095_model_source {E H VE TH} _ _.
Arguments q1306095_to_model {E H VE TH} _ _.
Arguments q1306095_from_model {E H VE TH} _ _.

Record q1306095_chart
    {H M : Type}
    (TH : q1306095_topological_space H)
    (TM : q1306095_topological_space M) : Type := {
  q1306095_chart_source : q1306095_set M;
  q1306095_chart_target : q1306095_set H;
  q1306095_chart_to : M -> H;
  q1306095_chart_from : H -> M;
  q1306095_chart_source_open :
    q1306095_is_open TM q1306095_chart_source;
  q1306095_chart_target_open :
    q1306095_is_open TH q1306095_chart_target;
  q1306095_chart_to_target :
    forall x : M,
      q1306095_chart_source x ->
      q1306095_chart_target (q1306095_chart_to x);
  q1306095_chart_from_source :
    forall h : H,
      q1306095_chart_target h ->
      q1306095_chart_source (q1306095_chart_from h);
  q1306095_chart_left_inverse :
    forall x : M,
      q1306095_chart_source x ->
      q1306095_chart_from (q1306095_chart_to x) = x;
  q1306095_chart_right_inverse :
    forall h : H,
      q1306095_chart_target h ->
      q1306095_chart_to (q1306095_chart_from h) = h;
  q1306095_chart_to_continuous :
    q1306095_continuous_on
      TM TH q1306095_chart_source q1306095_chart_to;
  q1306095_chart_from_continuous :
    q1306095_continuous_on
      TH TM q1306095_chart_target q1306095_chart_from
}.

Arguments q1306095_chart_source {H M TH TM} _ _.
Arguments q1306095_chart_target {H M TH TM} _ _.
Arguments q1306095_chart_to {H M TH TM} _ _.
Arguments q1306095_chart_from {H M TH TM} _ _.

Fixpoint q1306095_iterated
    (E F : Type) (order : nat) : Type :=
  match order with
  | O => F
  | S k => E -> q1306095_iterated E F k
  end.

Fixpoint q1306095_iterated_eq
    {E F : Type}
    (order : nat) :
    q1306095_iterated E F order ->
    q1306095_iterated E F order -> Prop :=
  match order as k return
    q1306095_iterated E F k ->
    q1306095_iterated E F k -> Prop with
  | O => fun x y => x = y
  | S k =>
      fun f g =>
        forall v : E,
          q1306095_iterated_eq k (f v) (g v)
  end.

Fixpoint q1306095_iterated_add
    {E F : Type}
    (VF : q1306095_normed_real_vector_space F)
    (order : nat) :
    q1306095_iterated E F order ->
    q1306095_iterated E F order ->
    q1306095_iterated E F order :=
  match order as k return
    q1306095_iterated E F k ->
    q1306095_iterated E F k ->
    q1306095_iterated E F k with
  | O => fun x y => q1306095_add VF x y
  | S k =>
      fun f g v =>
        q1306095_iterated_add VF k (f v) (g v)
  end.

Fixpoint q1306095_iterated_neg
    {E F : Type}
    (VF : q1306095_normed_real_vector_space F)
    (order : nat) :
    q1306095_iterated E F order ->
    q1306095_iterated E F order :=
  match order as k return
    q1306095_iterated E F k ->
    q1306095_iterated E F k with
  | O => fun x => q1306095_neg VF x
  | S k =>
      fun f v => q1306095_iterated_neg VF k (f v)
  end.

Definition q1306095_iterated_sub
    {E F : Type}
    (VF : q1306095_normed_real_vector_space F)
    (order : nat)
    (x y : q1306095_iterated E F order) :
    q1306095_iterated E F order :=
  q1306095_iterated_add VF order x
    (q1306095_iterated_neg VF order y).

Fixpoint q1306095_iterated_smul
    {E F : Type}
    (VF : q1306095_normed_real_vector_space F)
    (order : nat) :
    R ->
    q1306095_iterated E F order ->
    q1306095_iterated E F order :=
  match order as k return
    R ->
    q1306095_iterated E F k ->
    q1306095_iterated E F k with
  | O => fun a x => q1306095_smul VF a x
  | S k =>
      fun a f v => q1306095_iterated_smul VF k a (f v)
  end.

Fixpoint q1306095_multilinear
    {E F : Type}
    (VE : q1306095_normed_real_vector_space E)
    (VF : q1306095_normed_real_vector_space F)
    (order : nat)
    (D : q1306095_iterated E F order) : Prop :=
  match order as k return q1306095_iterated E F k -> Prop with
  | O => fun _ => True
  | S k =>
      fun L =>
        (forall v : E, q1306095_multilinear VE VF k (L v)) /\
        (forall x y : E,
          q1306095_iterated_eq k
            (L (q1306095_add VE x y))
            (q1306095_iterated_add VF k (L x) (L y))) /\
        (forall (a : R) (x : E),
          q1306095_iterated_eq k
            (L (q1306095_smul VE a x))
            (q1306095_iterated_smul VF k a (L x)))
  end D.

Fixpoint q1306095_iterated_bound
    {E F : Type}
    (VE : q1306095_normed_real_vector_space E)
    (VF : q1306095_normed_real_vector_space F)
    (order : nat)
    (D : q1306095_iterated E F order)
    (bound : R) : Prop :=
  match order as k return
    q1306095_iterated E F k -> Prop with
  | O => fun value => q1306095_norm VF value <= bound
  | S k =>
      fun L =>
        forall v : E,
          q1306095_norm VE v <= 1 ->
          q1306095_iterated_bound VE VF k (L v) bound
  end D.

Definition q1306095_is_smooth_data
    {E F : Type}
    (VE : q1306095_normed_real_vector_space E)
    (VF : q1306095_normed_real_vector_space F)
    (source : q1306095_set E)
    (f : E -> F)
    (D : forall order : nat,
      E -> q1306095_iterated E F order) : Prop :=
  (forall x : E, source x -> D O x = f x) /\
  (forall (order : nat) (x : E),
    source x ->
    q1306095_multilinear VE VF (S order) (D (S order) x) /\
    exists bound : R,
      0 <= bound /\
      q1306095_iterated_bound
        VE VF (S order) (D (S order) x) bound) /\
  forall (order : nat) (x : E),
    source x ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall y : E,
          source y ->
          q1306095_norm VE (q1306095_sub VE y x) < delta ->
          q1306095_iterated_bound VE VF order
            (q1306095_iterated_sub VF order
              (q1306095_iterated_sub VF order
                (D order y) (D order x))
              (D (S order) x (q1306095_sub VE y x)))
            (epsilon *
              q1306095_norm VE (q1306095_sub VE y x)).

Definition q1306095_smooth_on
    {E F : Type}
    (VE : q1306095_normed_real_vector_space E)
    (VF : q1306095_normed_real_vector_space F)
    (source : q1306095_set E)
    (f : E -> F) : Prop :=
  exists D : forall order : nat,
      E -> q1306095_iterated E F order,
    q1306095_is_smooth_data VE VF source f D.

Record q1306095_smooth_atlas
    {E H M : Type}
    (VE : q1306095_normed_real_vector_space E)
    (TH : q1306095_topological_space H)
    (TM : q1306095_topological_space M)
    (I : q1306095_model_with_corners VE TH) : Type := {
  q1306095_atlas_chart : M -> q1306095_chart TH TM;
  q1306095_atlas_chart_mem :
    forall x : M,
      q1306095_chart_source (q1306095_atlas_chart x) x;
  q1306095_atlas_compatible :
    forall x y : M,
      q1306095_smooth_on VE VE
        (fun u : E =>
          q1306095_model_source I u /\
          q1306095_chart_target
            (q1306095_atlas_chart x)
            (q1306095_to_model I u) /\
          q1306095_chart_source
            (q1306095_atlas_chart y)
            (q1306095_chart_from
              (q1306095_atlas_chart x)
              (q1306095_to_model I u)))
        (fun u : E =>
          q1306095_from_model I
            (q1306095_chart_to
              (q1306095_atlas_chart y)
              (q1306095_chart_from
                (q1306095_atlas_chart x)
                (q1306095_to_model I u))))
}.

Arguments q1306095_atlas_chart {E H M VE TH TM I} _ _.

Definition q1306095_euclidean (n : nat) : Type :=
  Fin.t n -> R.

Definition q1306095_euclidean_zero
    (n : nat) : q1306095_euclidean n :=
  fun _ => 0.

Definition q1306095_euclidean_add
    {n : nat}
    (x y : q1306095_euclidean n) : q1306095_euclidean n :=
  fun i => x i + y i.

Definition q1306095_euclidean_neg
    {n : nat}
    (x : q1306095_euclidean n) : q1306095_euclidean n :=
  fun i => - x i.

Definition q1306095_euclidean_smul
    {n : nat}
    (a : R) (x : q1306095_euclidean n) : q1306095_euclidean n :=
  fun i => a * x i.

Fixpoint q1306095_euclidean_sumsq
    (n : nat) : q1306095_euclidean n -> R :=
  match n as k return q1306095_euclidean k -> R with
  | O => fun _ => 0
  | S k =>
      fun x =>
        x Fin.F1 * x Fin.F1 +
        @q1306095_euclidean_sumsq k
          (fun i => x (Fin.FS i))
  end.

Definition q1306095_euclidean_norm
    {n : nat}
    (x : q1306095_euclidean n) : R :=
  sqrt (@q1306095_euclidean_sumsq n x).

Definition q1306095_standard_euclidean_structure
    (n : nat)
    (V : q1306095_normed_real_vector_space
      (q1306095_euclidean n)) : Prop :=
  q1306095_zero V = @q1306095_euclidean_zero n /\
  (forall x y : q1306095_euclidean n,
    q1306095_add V x y = q1306095_euclidean_add x y) /\
  (forall x : q1306095_euclidean n,
    q1306095_neg V x = q1306095_euclidean_neg x) /\
  (forall (a : R) (x : q1306095_euclidean n),
    q1306095_smul V a x = q1306095_euclidean_smul a x) /\
  forall x : q1306095_euclidean n,
    q1306095_norm V x = q1306095_euclidean_norm x.

Definition q1306095_smooth_map_with_derivative
    {E H M F : Type}
    (VE : q1306095_normed_real_vector_space E)
    (VF : q1306095_normed_real_vector_space F)
    (TH : q1306095_topological_space H)
    (TM : q1306095_topological_space M)
    (I : q1306095_model_with_corners VE TH)
    (A : @q1306095_smooth_atlas E H M VE TH TM I)
    (f : M -> F)
    (derivative :
      M -> q1306095_continuous_linear_map VE VF) : Prop :=
  forall x : M,
    exists D : forall order : nat,
        E -> q1306095_iterated E F order,
      q1306095_is_smooth_data VE VF
        (fun u : E =>
          q1306095_model_source I u /\
          q1306095_chart_target
            (q1306095_atlas_chart A x)
            (q1306095_to_model I u))
        (fun u : E =>
          f
            (q1306095_chart_from
              (q1306095_atlas_chart A x)
              (q1306095_to_model I u)))
        D /\
      forall v : E,
        D (S O)
          (q1306095_from_model I
            (q1306095_chart_to
              (q1306095_atlas_chart A x) x)) v =
        q1306095_clm_fun (derivative x) v.

Definition q1306095_closed_embedding
    {M F : Type}
    (TM : q1306095_topological_space M)
    (VF : q1306095_normed_real_vector_space F)
    (f : M -> F) : Prop :=
  (forall x y : M, f x = f y -> x = y) /\
  (forall V : q1306095_set F,
    q1306095_norm_open VF V ->
    q1306095_is_open TM (fun x : M => V (f x))) /\
  (forall U : q1306095_set M,
    q1306095_is_open TM U ->
    exists V : q1306095_set F,
      q1306095_norm_open VF V /\
      forall x : M, U x <-> V (f x)) /\
  q1306095_norm_open VF
    (fun y : F => ~ exists x : M, f x = y).

Definition q1306095_injective
    {X Y : Type} (f : X -> Y) : Prop :=
  forall x y : X, f x = f y -> x = y.

Theorem exists_embedding_euclidean_of_compact :
  forall (E : Type)
         (VE : q1306095_normed_real_vector_space E)
         (_ : q1306095_finite_dimensional VE)
         (H : Type)
         (TH : q1306095_topological_space H)
         (I : q1306095_model_with_corners VE TH)
         (M : Type)
         (TM : q1306095_topological_space M)
         (A : @q1306095_smooth_atlas E H M VE TH TM I),
    q1306095_hausdorff TM ->
    q1306095_compact TM ->
    exists n : nat,
    exists VN : q1306095_normed_real_vector_space
      (q1306095_euclidean n),
      @q1306095_standard_euclidean_structure n VN /\
      exists e : M -> q1306095_euclidean n,
      exists de :
        M -> q1306095_continuous_linear_map VE VN,
        @q1306095_smooth_map_with_derivative
          E H M (q1306095_euclidean n)
          VE VN TH TM I A e de /\
        @q1306095_closed_embedding
          M (q1306095_euclidean n) TM VN e /\
        forall x : M,
          @q1306095_injective
            E (q1306095_euclidean n)
            (q1306095_clm_fun (de x)).
Admitted.
