(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5445112
  (thousand-theorems__rocq__Q5445112), "Fernique's theorem": every Gaussian
  measure on a complete second-countable real normed space with its Borel
  measurable structure integrates exp (C * ||x||^2) for some C > 0. This file
  contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q5445112_set (A : Type) : Type := A -> Prop.

Definition q5445112_empty {A : Type} : q5445112_set A :=
  fun _ => False.

Definition q5445112_complement {A : Type}
    (E : q5445112_set A) : q5445112_set A :=
  fun x => ~ E x.

Definition q5445112_countable_union {A : Type}
    (E : nat -> q5445112_set A) : q5445112_set A :=
  fun x => exists n : nat, E n x.

Definition q5445112_preimage {A B : Type}
    (f : A -> B) (E : q5445112_set B) : q5445112_set A :=
  fun x => E (f x).

Definition q5445112_same_set {A : Type}
    (E F : q5445112_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q5445112_subset {A : Type}
    (E F : q5445112_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q5445112_disjoint {A : Type}
    (E F : q5445112_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q5445112_pairwise_disjoint {A : Type}
    (E : nat -> q5445112_set A) : Prop :=
  forall i j : nat, i <> j -> q5445112_disjoint (E i) (E j).

Inductive q5445112_ennreal : Type :=
| q5445112_ennreal_finite :
    forall value : R, 0 <= value -> q5445112_ennreal
| q5445112_ennreal_infinity : q5445112_ennreal.

Arguments q5445112_ennreal_finite value nonnegative : clear implicits.

Definition q5445112_ennreal_zero : q5445112_ennreal :=
  q5445112_ennreal_finite 0 (Rle_refl 0).

Definition q5445112_ennreal_one : q5445112_ennreal :=
  q5445112_ennreal_finite 1 Rle_0_1.

Definition q5445112_ennreal_eq
    (x y : q5445112_ennreal) : Prop :=
  match x, y with
  | q5445112_ennreal_finite a _,
    q5445112_ennreal_finite b _ => a = b
  | q5445112_ennreal_infinity,
    q5445112_ennreal_infinity => True
  | _, _ => False
  end.

Definition q5445112_ennreal_le
    (x y : q5445112_ennreal) : Prop :=
  match x, y with
  | q5445112_ennreal_finite a _,
    q5445112_ennreal_finite b _ => a <= b
  | q5445112_ennreal_finite _ _,
    q5445112_ennreal_infinity => True
  | q5445112_ennreal_infinity,
    q5445112_ennreal_finite _ _ => False
  | q5445112_ennreal_infinity,
    q5445112_ennreal_infinity => True
  end.

Definition q5445112_ennreal_add
    (x y : q5445112_ennreal) : q5445112_ennreal :=
  match x, y with
  | q5445112_ennreal_finite a ha,
    q5445112_ennreal_finite b hb =>
      q5445112_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q5445112_ennreal_infinity
  end.

Definition q5445112_ennreal_mul
    (x y : q5445112_ennreal) : q5445112_ennreal :=
  match x, y with
  | q5445112_ennreal_finite a ha,
    q5445112_ennreal_finite b hb =>
      q5445112_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q5445112_ennreal_finite a _, q5445112_ennreal_infinity
  | q5445112_ennreal_infinity, q5445112_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q5445112_ennreal_zero
      else q5445112_ennreal_infinity
  | q5445112_ennreal_infinity, q5445112_ennreal_infinity =>
      q5445112_ennreal_infinity
  end.

Definition q5445112_ennreal_of_real (x : R) : q5445112_ennreal :=
  q5445112_ennreal_finite (Rmax x 0) (Rmax_r x 0).

Fixpoint q5445112_ennreal_partial_sum
    (u : nat -> q5445112_ennreal)
    (n : nat) : q5445112_ennreal :=
  match n with
  | O => q5445112_ennreal_zero
  | S k =>
      q5445112_ennreal_add
        (q5445112_ennreal_partial_sum u k) (u k)
  end.

Definition q5445112_ennreal_supremum
    (values : q5445112_ennreal -> Prop)
    (bound : q5445112_ennreal) : Prop :=
  (forall value : q5445112_ennreal,
      values value -> q5445112_ennreal_le value bound) /\
  (forall upper : q5445112_ennreal,
      (forall value : q5445112_ennreal,
        values value -> q5445112_ennreal_le value upper) ->
      q5445112_ennreal_le bound upper).

Definition q5445112_ennreal_series_sum
    (u : nat -> q5445112_ennreal)
    (sum : q5445112_ennreal) : Prop :=
  q5445112_ennreal_supremum
    (fun value =>
      exists n : nat,
        q5445112_ennreal_eq value
          (q5445112_ennreal_partial_sum u n))
    sum.

Definition q5445112_ennreal_finite_value
    (x : q5445112_ennreal) : Prop :=
  exists value : R,
    exists nonnegative : 0 <= value,
      q5445112_ennreal_eq x
        (q5445112_ennreal_finite value nonnegative).

Record q5445112_measurable_space (A : Type) : Type := {
  q5445112_measurable : q5445112_set A -> Prop;
  q5445112_measurable_extensional :
    forall E F : q5445112_set A,
      q5445112_same_set E F ->
      (q5445112_measurable E <-> q5445112_measurable F);
  q5445112_measurable_empty :
    q5445112_measurable q5445112_empty;
  q5445112_measurable_complement :
    forall E : q5445112_set A,
      q5445112_measurable E ->
      q5445112_measurable (q5445112_complement E);
  q5445112_measurable_countable_union :
    forall E : nat -> q5445112_set A,
      (forall n : nat, q5445112_measurable (E n)) ->
      q5445112_measurable (q5445112_countable_union E)
}.

Arguments q5445112_measurable {A} _ _.

Record q5445112_measure {A : Type}
    (m : q5445112_measurable_space A) : Type := {
  q5445112_measure_value : q5445112_set A -> q5445112_ennreal;
  q5445112_measure_extensional :
    forall E F : q5445112_set A,
      q5445112_same_set E F ->
      q5445112_ennreal_eq
        (q5445112_measure_value E)
        (q5445112_measure_value F);
  q5445112_measure_empty :
    q5445112_ennreal_eq
      (q5445112_measure_value q5445112_empty)
      q5445112_ennreal_zero;
  q5445112_measure_countable_additive :
    forall E : nat -> q5445112_set A,
      (forall n : nat, q5445112_measurable m (E n)) ->
      q5445112_pairwise_disjoint E ->
      q5445112_ennreal_series_sum
        (fun n => q5445112_measure_value (E n))
        (q5445112_measure_value (q5445112_countable_union E))
}.

Arguments q5445112_measure_value {A m} _ _.

Record q5445112_normed_real_vector_space (E : Type) : Type := {
  q5445112_zero : E;
  q5445112_add : E -> E -> E;
  q5445112_neg : E -> E;
  q5445112_smul : R -> E -> E;
  q5445112_norm : E -> R;
  q5445112_add_assoc :
    forall x y z : E,
      q5445112_add x (q5445112_add y z) =
      q5445112_add (q5445112_add x y) z;
  q5445112_add_comm :
    forall x y : E, q5445112_add x y = q5445112_add y x;
  q5445112_add_zero :
    forall x : E, q5445112_add x q5445112_zero = x;
  q5445112_add_neg :
    forall x : E,
      q5445112_add x (q5445112_neg x) = q5445112_zero;
  q5445112_one_smul :
    forall x : E, q5445112_smul 1 x = x;
  q5445112_mul_smul :
    forall (a b : R) (x : E),
      q5445112_smul (a * b) x =
      q5445112_smul a (q5445112_smul b x);
  q5445112_add_smul :
    forall (a b : R) (x : E),
      q5445112_smul (a + b) x =
      q5445112_add (q5445112_smul a x) (q5445112_smul b x);
  q5445112_smul_add :
    forall (a : R) (x y : E),
      q5445112_smul a (q5445112_add x y) =
      q5445112_add (q5445112_smul a x) (q5445112_smul a y);
  q5445112_zero_smul :
    forall x : E, q5445112_smul 0 x = q5445112_zero;
  q5445112_smul_zero :
    forall a : R, q5445112_smul a q5445112_zero = q5445112_zero;
  q5445112_norm_nonnegative :
    forall x : E, 0 <= q5445112_norm x;
  q5445112_norm_eq_zero :
    forall x : E, q5445112_norm x = 0 <-> x = q5445112_zero;
  q5445112_norm_add_le :
    forall x y : E,
      q5445112_norm (q5445112_add x y) <=
      q5445112_norm x + q5445112_norm y;
  q5445112_norm_smul :
    forall (a : R) (x : E),
      q5445112_norm (q5445112_smul a x) =
      Rabs a * q5445112_norm x
}.

Arguments q5445112_zero {E} _.
Arguments q5445112_add {E} _ _ _.
Arguments q5445112_neg {E} _ _.
Arguments q5445112_smul {E} _ _ _.
Arguments q5445112_norm {E} _ _.

Definition q5445112_sub {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (x y : E) : E :=
  q5445112_add V x (q5445112_neg V y).

Definition q5445112_open_ball {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (center : E) (radius : R) : q5445112_set E :=
  fun x => q5445112_norm V (q5445112_sub V x center) < radius.

Definition q5445112_open {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (U : q5445112_set E) : Prop :=
  forall x : E,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      q5445112_subset (q5445112_open_ball V x epsilon) U.

Definition q5445112_second_countable {E : Type}
    (V : q5445112_normed_real_vector_space E) : Prop :=
  exists basis : nat -> q5445112_set E,
    (forall n : nat, q5445112_open V (basis n)) /\
    forall (U : q5445112_set E) (x : E),
      q5445112_open V U ->
      U x ->
      exists n : nat,
        basis n x /\ q5445112_subset (basis n) U.

Definition q5445112_sequence_converges {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q5445112_norm V (q5445112_sub V (u n) limit) < epsilon.

Definition q5445112_sequence_cauchy {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q5445112_norm V (q5445112_sub V (u m) (u n)) < epsilon.

Definition q5445112_complete {E : Type}
    (V : q5445112_normed_real_vector_space E) : Prop :=
  forall u : nat -> E,
    q5445112_sequence_cauchy V u ->
    exists limit : E, q5445112_sequence_converges V u limit.

Definition q5445112_borel_measurable {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (S : q5445112_set E) : Prop :=
  forall sigma : q5445112_measurable_space E,
    (forall U : q5445112_set E,
      q5445112_open V U ->
      q5445112_measurable sigma U) ->
    q5445112_measurable sigma S.

Definition q5445112_borel_space {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (m : q5445112_measurable_space E) : Prop :=
  forall S : q5445112_set E,
    q5445112_measurable m S <->
    q5445112_borel_measurable V S.

Definition q5445112_real_open (U : q5445112_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R, Rabs (y - x) < epsilon -> U y.

Definition q5445112_real_borel_measurable
    (S : q5445112_set R) : Prop :=
  forall sigma : q5445112_measurable_space R,
    (forall U : q5445112_set R,
      q5445112_real_open U ->
      q5445112_measurable sigma U) ->
    q5445112_measurable sigma S.

Definition q5445112_real_borel_space
    (m : q5445112_measurable_space R) : Prop :=
  forall S : q5445112_set R,
    q5445112_measurable m S <->
    q5445112_real_borel_measurable S.

Definition q5445112_almost_everywhere {A : Type}
    {m : q5445112_measurable_space A}
    (mu : q5445112_measure m)
    (P : A -> Prop) : Prop :=
  exists null_set : q5445112_set A,
    q5445112_measurable m null_set /\
    q5445112_ennreal_eq
      (q5445112_measure_value mu null_set)
      q5445112_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Definition q5445112_measurable_real_function {A : Type}
    (m : q5445112_measurable_space A)
    (f : A -> R) : Prop :=
  forall B : q5445112_set R,
    q5445112_real_borel_measurable B ->
    q5445112_measurable m (q5445112_preimage f B).

Definition q5445112_ae_measurable_real_function {A : Type}
    {m : q5445112_measurable_space A}
    (mu : q5445112_measure m)
    (f : A -> R) : Prop :=
  exists g : A -> R,
    q5445112_measurable_real_function m g /\
    q5445112_almost_everywhere mu (fun x => f x = g x).

Definition q5445112_finite_partition {A : Type}
    {m : q5445112_measurable_space A}
    (mu : q5445112_measure m)
    (k : nat) (cells : nat -> q5445112_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q5445112_measurable m (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q5445112_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Record q5445112_nonnegative_real : Type := {
  q5445112_nnreal_value : R;
  q5445112_nnreal_nonnegative : 0 <= q5445112_nnreal_value
}.

Definition q5445112_ennreal_of_nonnegative
    (x : q5445112_nonnegative_real) : q5445112_ennreal :=
  q5445112_ennreal_finite
    (q5445112_nnreal_value x)
    (q5445112_nnreal_nonnegative x).

Definition q5445112_simple_lintegral_below {A : Type}
    {m : q5445112_measurable_space A}
    (mu : q5445112_measure m)
    (f : A -> q5445112_ennreal)
    (value : q5445112_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q5445112_nonnegative_real)
         (cells : nat -> q5445112_set A),
    q5445112_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q5445112_ennreal_le
        (q5445112_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q5445112_ennreal_eq value
      (q5445112_ennreal_partial_sum
        (fun i =>
          q5445112_ennreal_mul
            (q5445112_ennreal_of_nonnegative (coefficients i))
            (q5445112_measure_value mu (cells i)))
        k).

Definition q5445112_lintegral_has_value {A : Type}
    {m : q5445112_measurable_space A}
    (mu : q5445112_measure m)
    (f : A -> q5445112_ennreal)
    (value : q5445112_ennreal) : Prop :=
  q5445112_ennreal_supremum
    (q5445112_simple_lintegral_below mu f) value.

Definition q5445112_absolute_ennreal (x : R) : q5445112_ennreal :=
  q5445112_ennreal_finite (Rabs x) (Rabs_pos x).

Definition q5445112_integrable_real {A : Type}
    {m : q5445112_measurable_space A}
    (mu : q5445112_measure m)
    (f : A -> R) : Prop :=
  q5445112_ae_measurable_real_function mu f /\
  exists value : q5445112_ennreal,
    q5445112_lintegral_has_value mu
      (fun x => q5445112_absolute_ennreal (f x)) value /\
    q5445112_ennreal_finite_value value.

Definition q5445112_continuous_linear_functional {E : Type}
    (V : q5445112_normed_real_vector_space E)
    (ell : E -> R) : Prop :=
  (forall x y : E,
    ell (q5445112_add V x y) = ell x + ell y) /\
  (forall (a : R) (x : E),
    ell (q5445112_smul V a x) = a * ell x) /\
  exists bound : R,
    0 <= bound /\
    forall x : E,
      Rabs (ell x) <= bound * q5445112_norm V x.

Definition q5445112_interval_closed_open
    (a b : R) : q5445112_set R :=
  fun x => a <= x /\ x < b.

Definition q5445112_is_lebesgue_measure
    {m : q5445112_measurable_space R}
    (lambda : q5445112_measure m) : Prop :=
  q5445112_real_borel_space m /\
  forall a b : R,
    a <= b ->
    q5445112_ennreal_eq
      (q5445112_measure_value lambda
        (q5445112_interval_closed_open a b))
      (q5445112_ennreal_of_real (b - a)).

Definition q5445112_indicator_ennreal {A : Type}
    (S : q5445112_set A)
    (f : A -> R)
    (x : A) : q5445112_ennreal :=
  if excluded_middle_informative (S x)
  then q5445112_ennreal_of_real (f x)
  else q5445112_ennreal_zero.

Definition q5445112_dirac_value
    (point : R) (S : q5445112_set R) : q5445112_ennreal :=
  if excluded_middle_informative (S point)
  then q5445112_ennreal_one
  else q5445112_ennreal_zero.

Definition q5445112_gaussian_density
    (mean variance x : R) : R :=
  exp (- ((x - mean) ^ 2) / (2 * variance)) /
  sqrt (2 * PI * variance).

Definition q5445112_gaussian_real_measure
    {m : q5445112_measurable_space R}
    (nu : q5445112_measure m) : Prop :=
  q5445112_real_borel_space m /\
  exists mean variance : R,
    0 <= variance /\
    ((variance = 0 /\
      forall S : q5445112_set R,
        q5445112_measurable m S ->
        q5445112_ennreal_eq
          (q5445112_measure_value nu S)
          (q5445112_dirac_value mean S)) \/
     (0 < variance /\
      exists lambda : q5445112_measure m,
        q5445112_is_lebesgue_measure lambda /\
        forall S : q5445112_set R,
          q5445112_measurable m S ->
          exists value : q5445112_ennreal,
            q5445112_lintegral_has_value lambda
              (q5445112_indicator_ennreal S
                (q5445112_gaussian_density mean variance))
              value /\
            q5445112_ennreal_eq
              (q5445112_measure_value nu S) value)).

Definition q5445112_is_pushforward {A B : Type}
    {mA : q5445112_measurable_space A}
    {mB : q5445112_measurable_space B}
    (mu : q5445112_measure mA)
    (nu : q5445112_measure mB)
    (f : A -> B) : Prop :=
  (forall S : q5445112_set B,
    q5445112_measurable mB S ->
    q5445112_measurable mA (q5445112_preimage f S)) /\
  forall S : q5445112_set B,
    q5445112_measurable mB S ->
    q5445112_ennreal_eq
      (q5445112_measure_value nu S)
      (q5445112_measure_value mu (q5445112_preimage f S)).

Definition q5445112_is_gaussian {E : Type}
    (V : q5445112_normed_real_vector_space E)
    {m : q5445112_measurable_space E}
    (mu : q5445112_measure m) : Prop :=
  exists real_borel : q5445112_measurable_space R,
    q5445112_real_borel_space real_borel /\
    forall ell : E -> R,
      q5445112_continuous_linear_functional V ell ->
      exists nu : q5445112_measure real_borel,
        q5445112_is_pushforward mu nu ell /\
        q5445112_gaussian_real_measure nu.

Theorem exists_integrable_exp_sq :
  forall (E : Type)
         (V : q5445112_normed_real_vector_space E)
         (m : q5445112_measurable_space E)
         (mu : q5445112_measure m),
    q5445112_complete V ->
    q5445112_second_countable V ->
    q5445112_borel_space V m ->
    q5445112_is_gaussian V mu ->
    exists C : R,
      0 < C /\
      q5445112_integrable_real mu
        (fun x => exp (C * (q5445112_norm V x) ^ 2)).
Admitted.
