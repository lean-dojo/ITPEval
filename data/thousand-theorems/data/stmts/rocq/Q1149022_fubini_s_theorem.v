(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1149022
  (thousand-theorems__rocq__Q1149022), "Fubini's theorem": for an integrable
  normed-real-vector-space-valued function on the product of two s-finite
  measure spaces, its Bochner integral equals the iterated Bochner integral.
  This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1149022_set (A : Type) : Type := A -> Prop.

Definition q1149022_empty {A : Type} : q1149022_set A :=
  fun _ => False.

Definition q1149022_full {A : Type} : q1149022_set A :=
  fun _ => True.

Definition q1149022_complement {A : Type}
    (E : q1149022_set A) : q1149022_set A :=
  fun x => ~ E x.

Definition q1149022_countable_union {A : Type}
    (E : nat -> q1149022_set A) : q1149022_set A :=
  fun x => exists n : nat, E n x.

Definition q1149022_same_set {A : Type}
    (E F : q1149022_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1149022_disjoint {A : Type}
    (E F : q1149022_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1149022_pairwise_disjoint {A : Type}
    (E : nat -> q1149022_set A) : Prop :=
  forall i j : nat, i <> j -> q1149022_disjoint (E i) (E j).

Definition q1149022_sigma_class {A : Type}
    (C : q1149022_set (q1149022_set A)) : Prop :=
  C q1149022_empty /\
  (forall E F : q1149022_set A,
    q1149022_same_set E F ->
    C E ->
    C F) /\
  (forall E : q1149022_set A,
    C E -> C (q1149022_complement E)) /\
  (forall E : nat -> q1149022_set A,
    (forall n : nat, C (E n)) ->
    C (q1149022_countable_union E)).

Inductive q1149022_ennreal : Type :=
| q1149022_ennreal_finite :
    forall value : R, 0 <= value -> q1149022_ennreal
| q1149022_ennreal_infinity : q1149022_ennreal.

Arguments q1149022_ennreal_finite value nonnegative : clear implicits.

Definition q1149022_ennreal_zero : q1149022_ennreal :=
  q1149022_ennreal_finite 0 (Rle_refl 0).

Definition q1149022_ennreal_eq
    (x y : q1149022_ennreal) : Prop :=
  match x, y with
  | q1149022_ennreal_finite a _,
    q1149022_ennreal_finite b _ => a = b
  | q1149022_ennreal_infinity,
    q1149022_ennreal_infinity => True
  | _, _ => False
  end.

Definition q1149022_ennreal_le
    (x y : q1149022_ennreal) : Prop :=
  match x, y with
  | q1149022_ennreal_finite a _,
    q1149022_ennreal_finite b _ => a <= b
  | q1149022_ennreal_finite _ _,
    q1149022_ennreal_infinity => True
  | q1149022_ennreal_infinity,
    q1149022_ennreal_finite _ _ => False
  | q1149022_ennreal_infinity,
    q1149022_ennreal_infinity => True
  end.

Definition q1149022_ennreal_add
    (x y : q1149022_ennreal) : q1149022_ennreal :=
  match x, y with
  | q1149022_ennreal_finite a ha,
    q1149022_ennreal_finite b hb =>
      q1149022_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q1149022_ennreal_infinity
  end.

Definition q1149022_ennreal_mul
    (x y : q1149022_ennreal) : q1149022_ennreal :=
  match x, y with
  | q1149022_ennreal_finite a ha,
    q1149022_ennreal_finite b hb =>
      q1149022_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q1149022_ennreal_finite a _, q1149022_ennreal_infinity
  | q1149022_ennreal_infinity, q1149022_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q1149022_ennreal_zero
      else q1149022_ennreal_infinity
  | q1149022_ennreal_infinity, q1149022_ennreal_infinity =>
      q1149022_ennreal_infinity
  end.

Fixpoint q1149022_ennreal_partial_sum
    (u : nat -> q1149022_ennreal)
    (n : nat) : q1149022_ennreal :=
  match n with
  | O => q1149022_ennreal_zero
  | S k =>
      q1149022_ennreal_add
        (q1149022_ennreal_partial_sum u k) (u k)
  end.

Definition q1149022_ennreal_supremum
    (values : q1149022_ennreal -> Prop)
    (bound : q1149022_ennreal) : Prop :=
  (forall value : q1149022_ennreal,
      values value -> q1149022_ennreal_le value bound) /\
  (forall upper : q1149022_ennreal,
      (forall value : q1149022_ennreal,
        values value -> q1149022_ennreal_le value upper) ->
      q1149022_ennreal_le bound upper).

Definition q1149022_ennreal_series_sum
    (u : nat -> q1149022_ennreal)
    (sum : q1149022_ennreal) : Prop :=
  q1149022_ennreal_supremum
    (fun value =>
      exists n : nat,
        q1149022_ennreal_eq value
          (q1149022_ennreal_partial_sum u n))
    sum.

Definition q1149022_ennreal_represents
    (x : q1149022_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q1149022_ennreal_eq x
      (q1149022_ennreal_finite value nonnegative).

Definition q1149022_ennreal_finite_value
    (x : q1149022_ennreal) : Prop :=
  exists value : R, q1149022_ennreal_represents x value.

Record q1149022_measure_space (A : Type) : Type := {
  q1149022_measurable : q1149022_set A -> Prop;
  q1149022_measurable_extensional :
    forall E F : q1149022_set A,
      q1149022_same_set E F ->
      (q1149022_measurable E <-> q1149022_measurable F);
  q1149022_measurable_empty :
    q1149022_measurable q1149022_empty;
  q1149022_measurable_complement :
    forall E : q1149022_set A,
      q1149022_measurable E ->
      q1149022_measurable (q1149022_complement E);
  q1149022_measurable_countable_union :
    forall E : nat -> q1149022_set A,
      (forall n : nat, q1149022_measurable (E n)) ->
      q1149022_measurable (q1149022_countable_union E);
  q1149022_measure : q1149022_set A -> q1149022_ennreal;
  q1149022_measure_extensional :
    forall E F : q1149022_set A,
      q1149022_same_set E F ->
      q1149022_ennreal_eq
        (q1149022_measure E) (q1149022_measure F);
  q1149022_measure_empty :
    q1149022_ennreal_eq
      (q1149022_measure q1149022_empty)
      q1149022_ennreal_zero;
  q1149022_measure_countable_additive :
    forall E : nat -> q1149022_set A,
      (forall n : nat, q1149022_measurable (E n)) ->
      q1149022_pairwise_disjoint E ->
      q1149022_ennreal_series_sum
        (fun n => q1149022_measure (E n))
        (q1149022_measure (q1149022_countable_union E))
}.

Arguments q1149022_measurable {A} _ _.
Arguments q1149022_measure {A} _ _.

Definition q1149022_same_measurable_space {A : Type}
    (mu nu : q1149022_measure_space A) : Prop :=
  forall E : q1149022_set A,
    q1149022_measurable mu E <-> q1149022_measurable nu E.

Definition q1149022_finite_measure {A : Type}
    (mu : q1149022_measure_space A) : Prop :=
  q1149022_ennreal_finite_value
    (q1149022_measure mu q1149022_full).

Definition q1149022_s_finite {A : Type}
    (mu : q1149022_measure_space A) : Prop :=
  exists components : nat -> q1149022_measure_space A,
    (forall n : nat,
      q1149022_same_measurable_space mu (components n) /\
      q1149022_finite_measure (components n)) /\
    forall E : q1149022_set A,
      q1149022_measurable mu E ->
      q1149022_ennreal_series_sum
        (fun n => q1149022_measure (components n) E)
        (q1149022_measure mu E).

Definition q1149022_rectangle {A B : Type}
    (E : q1149022_set A)
    (F : q1149022_set B) : q1149022_set (A * B) :=
  fun pair => E (fst pair) /\ F (snd pair).

Definition q1149022_product_measurable_set {A B : Type}
    (mu : q1149022_measure_space A)
    (nu : q1149022_measure_space B)
    (S : q1149022_set (A * B)) : Prop :=
  forall C : q1149022_set (q1149022_set (A * B)),
    q1149022_sigma_class C ->
    (forall (E : q1149022_set A) (F : q1149022_set B),
      q1149022_measurable mu E ->
      q1149022_measurable nu F ->
      C (q1149022_rectangle E F)) ->
    C S.

Definition q1149022_almost_everywhere {A : Type}
    (mu : q1149022_measure_space A)
    (P : A -> Prop) : Prop :=
  exists null_set : q1149022_set A,
    q1149022_measurable mu null_set /\
    q1149022_ennreal_eq
      (q1149022_measure mu null_set)
      q1149022_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Record q1149022_normed_real_vector_space (G : Type) : Type := {
  q1149022_zero : G;
  q1149022_add : G -> G -> G;
  q1149022_neg : G -> G;
  q1149022_smul : R -> G -> G;
  q1149022_norm : G -> R;
  q1149022_add_assoc :
    forall x y z : G,
      q1149022_add x (q1149022_add y z) =
      q1149022_add (q1149022_add x y) z;
  q1149022_add_comm :
    forall x y : G, q1149022_add x y = q1149022_add y x;
  q1149022_add_zero :
    forall x : G, q1149022_add x q1149022_zero = x;
  q1149022_add_neg :
    forall x : G,
      q1149022_add x (q1149022_neg x) = q1149022_zero;
  q1149022_one_smul :
    forall x : G, q1149022_smul 1 x = x;
  q1149022_mul_smul :
    forall (a b : R) (x : G),
      q1149022_smul (a * b) x =
      q1149022_smul a (q1149022_smul b x);
  q1149022_add_smul :
    forall (a b : R) (x : G),
      q1149022_smul (a + b) x =
      q1149022_add (q1149022_smul a x) (q1149022_smul b x);
  q1149022_smul_add :
    forall (a : R) (x y : G),
      q1149022_smul a (q1149022_add x y) =
      q1149022_add (q1149022_smul a x) (q1149022_smul a y);
  q1149022_zero_smul :
    forall x : G, q1149022_smul 0 x = q1149022_zero;
  q1149022_smul_zero :
    forall a : R, q1149022_smul a q1149022_zero = q1149022_zero;
  q1149022_norm_nonnegative :
    forall x : G, 0 <= q1149022_norm x;
  q1149022_norm_eq_zero :
    forall x : G,
      q1149022_norm x = 0 <-> x = q1149022_zero;
  q1149022_norm_add_le :
    forall x y : G,
      q1149022_norm (q1149022_add x y) <=
      q1149022_norm x + q1149022_norm y;
  q1149022_norm_smul :
    forall (a : R) (x : G),
      q1149022_norm (q1149022_smul a x) =
      Rabs a * q1149022_norm x
}.

Arguments q1149022_zero {G} _.
Arguments q1149022_add {G} _ _ _.
Arguments q1149022_neg {G} _ _.
Arguments q1149022_smul {G} _ _ _.
Arguments q1149022_norm {G} _ _.

Definition q1149022_sub {G : Type}
    (V : q1149022_normed_real_vector_space G)
    (x y : G) : G :=
  q1149022_add V x (q1149022_neg V y).

Definition q1149022_vector_sequence_converges {G : Type}
    (V : q1149022_normed_real_vector_space G)
    (u : nat -> G) (limit : G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1149022_norm V
          (q1149022_sub V (u n) limit) < epsilon.

Definition q1149022_vector_sequence_cauchy {G : Type}
    (V : q1149022_normed_real_vector_space G)
    (u : nat -> G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q1149022_norm V
          (q1149022_sub V (u m) (u n)) < epsilon.

Definition q1149022_complete {G : Type}
    (V : q1149022_normed_real_vector_space G) : Prop :=
  forall u : nat -> G,
    q1149022_vector_sequence_cauchy V u ->
    exists limit : G,
      q1149022_vector_sequence_converges V u limit.

Definition q1149022_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q1149022_finite_partition {A : Type}
    (mu : q1149022_measure_space A)
    (k : nat) (cells : nat -> q1149022_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q1149022_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q1149022_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q1149022_measurable_simple {A G : Type}
    (mu : q1149022_measure_space A)
    (s : A -> G) : Prop :=
  exists (k : nat) (coefficients : nat -> G)
         (cells : nat -> q1149022_set A),
    q1149022_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q1149022_ae_strongly_measurable {A G : Type}
    (V : q1149022_normed_real_vector_space G)
    (mu : q1149022_measure_space A)
    (f : A -> G) : Prop :=
  exists approximants : nat -> A -> G,
    (forall n : nat,
      q1149022_measurable_simple mu (approximants n)) /\
    q1149022_almost_everywhere mu
      (fun x =>
        q1149022_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q1149022_nonnegative_real : Type := {
  q1149022_nnreal_value : R;
  q1149022_nnreal_nonnegative : 0 <= q1149022_nnreal_value
}.

Definition q1149022_ennreal_of_nonnegative
    (x : q1149022_nonnegative_real) : q1149022_ennreal :=
  q1149022_ennreal_finite
    (q1149022_nnreal_value x)
    (q1149022_nnreal_nonnegative x).

Definition q1149022_simple_lintegral_below {A : Type}
    (mu : q1149022_measure_space A)
    (f : A -> q1149022_ennreal)
    (value : q1149022_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q1149022_nonnegative_real)
         (cells : nat -> q1149022_set A),
    q1149022_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q1149022_ennreal_le
        (q1149022_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q1149022_ennreal_eq value
      (q1149022_ennreal_partial_sum
        (fun i =>
          q1149022_ennreal_mul
            (q1149022_ennreal_of_nonnegative (coefficients i))
            (q1149022_measure mu (cells i)))
        k).

Definition q1149022_lintegral_has_value {A : Type}
    (mu : q1149022_measure_space A)
    (f : A -> q1149022_ennreal)
    (value : q1149022_ennreal) : Prop :=
  q1149022_ennreal_supremum
    (q1149022_simple_lintegral_below mu f) value.

Definition q1149022_vertical_section {A B : Type}
    (S : q1149022_set (A * B))
    (x : A) : q1149022_set B :=
  fun y => S (x, y).

Definition q1149022_is_product_measure {A B : Type}
    (mu : q1149022_measure_space A)
    (nu : q1149022_measure_space B)
    (product : q1149022_measure_space (A * B)) : Prop :=
  (forall S : q1149022_set (A * B),
    q1149022_measurable product S <->
    q1149022_product_measurable_set mu nu S) /\
  (forall S : q1149022_set (A * B),
    q1149022_measurable product S ->
    q1149022_lintegral_has_value mu
      (fun x =>
        q1149022_measure nu
          (q1149022_vertical_section S x))
      (q1149022_measure product S)).

Definition q1149022_norm_ennreal {G : Type}
    (V : q1149022_normed_real_vector_space G)
    (x : G) : q1149022_ennreal :=
  q1149022_ennreal_finite
    (q1149022_norm V x)
    (q1149022_norm_nonnegative V x).

Definition q1149022_integrable {A G : Type}
    (V : q1149022_normed_real_vector_space G)
    (mu : q1149022_measure_space A)
    (f : A -> G) : Prop :=
  q1149022_ae_strongly_measurable V mu f /\
  exists value : q1149022_ennreal,
    q1149022_lintegral_has_value mu
      (fun x => q1149022_norm_ennreal V (f x)) value /\
    q1149022_ennreal_finite_value value.

Fixpoint q1149022_vector_sum {G : Type}
    (V : q1149022_normed_real_vector_space G)
    (u : nat -> G) (n : nat) : G :=
  match n with
  | O => q1149022_zero V
  | S k =>
      q1149022_add V
        (q1149022_vector_sum V u k) (u k)
  end.

Definition q1149022_weighted_cell_value {A G : Type}
    (V : q1149022_normed_real_vector_space G)
    (mu : q1149022_measure_space A)
    (cell : q1149022_set A)
    (coefficient value : G) : Prop :=
  (coefficient = q1149022_zero V /\
    value = q1149022_zero V) \/
  exists mass : R,
    q1149022_ennreal_represents
      (q1149022_measure mu cell) mass /\
    value = q1149022_smul V mass coefficient.

Definition q1149022_simple_integral_has_value {A G : Type}
    (V : q1149022_normed_real_vector_space G)
    (mu : q1149022_measure_space A)
    (s : A -> G) (value : G) : Prop :=
  exists (k : nat) (coefficients terms : nat -> G)
         (cells : nat -> q1149022_set A),
    q1149022_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q1149022_weighted_cell_value
        V mu (cells i) (coefficients i) (terms i)) /\
    value = q1149022_vector_sum V terms k.

Definition q1149022_l1_approximates {A G : Type}
    (V : q1149022_normed_real_vector_space G)
    (mu : q1149022_measure_space A)
    (approximants : nat -> A -> G)
    (f : A -> G) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q1149022_ennreal,
        q1149022_lintegral_has_value mu
          (fun x =>
            q1149022_norm_ennreal V
              (q1149022_sub V (approximants n x) (f x)))
          integral_error /\
        q1149022_ennreal_represents
          integral_error (errors n)) /\
    q1149022_real_sequence_converges errors 0.

Definition q1149022_standard_bochner_integral_value {A G : Type}
    (V : q1149022_normed_real_vector_space G)
    (mu : q1149022_measure_space A)
    (f : A -> G) (value : G) : Prop :=
  exists (approximants : nat -> A -> G)
         (integrals : nat -> G),
    (forall n : nat,
      q1149022_measurable_simple mu (approximants n)) /\
    (forall n : nat,
      q1149022_simple_integral_has_value
        V mu (approximants n) (integrals n)) /\
    q1149022_l1_approximates V mu approximants f /\
    q1149022_vector_sequence_converges V integrals value.

Definition q1149022_bochner_integral {A G : Type}
    (V : q1149022_normed_real_vector_space G)
    (mu : q1149022_measure_space A)
    (f : A -> G) : G :=
  match excluded_middle_informative (q1149022_complete V) with
  | left _ =>
      match excluded_middle_informative
              (exists value : G,
                q1149022_standard_bochner_integral_value
                  V mu f value) with
      | left _ =>
          epsilon (inhabits (q1149022_zero V))
            (fun value : G =>
              q1149022_standard_bochner_integral_value
                V mu f value)
      | right _ => q1149022_zero V
      end
  | right _ => q1149022_zero V
  end.

Theorem integral_prod :
  forall (Alpha Beta G : Type)
         (V : q1149022_normed_real_vector_space G)
         (mu : q1149022_measure_space Alpha)
         (nu : q1149022_measure_space Beta)
         (product : q1149022_measure_space (Alpha * Beta))
         (f : Alpha * Beta -> G),
    q1149022_s_finite mu ->
    q1149022_s_finite nu ->
    q1149022_is_product_measure mu nu product ->
    q1149022_integrable V product f ->
    q1149022_bochner_integral V product f =
    q1149022_bochner_integral V mu
      (fun x =>
        q1149022_bochner_integral V nu
          (fun y => f (x, y))).
Admitted.
