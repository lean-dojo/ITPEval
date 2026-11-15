(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2027347
  (thousand-theorems__rocq__Q2027347), "Optional stopping theorem": a strongly
  adapted integrable real process is a submartingale exactly when expectations
  of its stopped values are monotone for ordered bounded stopping times. This
  file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q2027347_set (A : Type) : Type := A -> Prop.

Definition q2027347_empty {A : Type} : q2027347_set A :=
  fun _ => False.

Definition q2027347_full {A : Type} : q2027347_set A :=
  fun _ => True.

Definition q2027347_complement {A : Type}
    (E : q2027347_set A) : q2027347_set A :=
  fun x => ~ E x.

Definition q2027347_countable_union {A : Type}
    (E : nat -> q2027347_set A) : q2027347_set A :=
  fun x => exists n : nat, E n x.

Definition q2027347_same_set {A : Type}
    (E F : q2027347_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q2027347_disjoint {A : Type}
    (E F : q2027347_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q2027347_pairwise_disjoint {A : Type}
    (E : nat -> q2027347_set A) : Prop :=
  forall i j : nat,
    i <> j -> q2027347_disjoint (E i) (E j).

Record q2027347_measurable_space (A : Type) : Type := {
  q2027347_measurable : q2027347_set A -> Prop;
  q2027347_measurable_extensional :
    forall E F : q2027347_set A,
      q2027347_same_set E F ->
      (q2027347_measurable E <-> q2027347_measurable F);
  q2027347_measurable_empty :
    q2027347_measurable q2027347_empty;
  q2027347_measurable_complement :
    forall E : q2027347_set A,
      q2027347_measurable E ->
      q2027347_measurable (q2027347_complement E);
  q2027347_measurable_countable_union :
    forall E : nat -> q2027347_set A,
      (forall n : nat, q2027347_measurable (E n)) ->
      q2027347_measurable (q2027347_countable_union E)
}.

Arguments q2027347_measurable {A} _ _.

Inductive q2027347_ennreal : Type :=
| q2027347_ennreal_finite :
    forall value : R, 0 <= value -> q2027347_ennreal
| q2027347_ennreal_infinity : q2027347_ennreal.

Arguments q2027347_ennreal_finite value nonnegative : clear implicits.

Definition q2027347_ennreal_zero : q2027347_ennreal :=
  q2027347_ennreal_finite 0 (Rle_refl 0).

Definition q2027347_ennreal_eq
    (x y : q2027347_ennreal) : Prop :=
  match x, y with
  | q2027347_ennreal_finite a _,
    q2027347_ennreal_finite b _ => a = b
  | q2027347_ennreal_infinity,
    q2027347_ennreal_infinity => True
  | _, _ => False
  end.

Definition q2027347_ennreal_le
    (x y : q2027347_ennreal) : Prop :=
  match x, y with
  | q2027347_ennreal_finite a _,
    q2027347_ennreal_finite b _ => a <= b
  | q2027347_ennreal_finite _ _,
    q2027347_ennreal_infinity => True
  | q2027347_ennreal_infinity,
    q2027347_ennreal_finite _ _ => False
  | q2027347_ennreal_infinity,
    q2027347_ennreal_infinity => True
  end.

Definition q2027347_ennreal_add
    (x y : q2027347_ennreal) : q2027347_ennreal :=
  match x, y with
  | q2027347_ennreal_finite a ha,
    q2027347_ennreal_finite b hb =>
      q2027347_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q2027347_ennreal_infinity
  end.

Definition q2027347_ennreal_mul
    (x y : q2027347_ennreal) : q2027347_ennreal :=
  match x, y with
  | q2027347_ennreal_finite a ha,
    q2027347_ennreal_finite b hb =>
      q2027347_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q2027347_ennreal_finite a _, q2027347_ennreal_infinity
  | q2027347_ennreal_infinity, q2027347_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q2027347_ennreal_zero
      else q2027347_ennreal_infinity
  | q2027347_ennreal_infinity, q2027347_ennreal_infinity =>
      q2027347_ennreal_infinity
  end.

Fixpoint q2027347_ennreal_partial_sum
    (u : nat -> q2027347_ennreal)
    (n : nat) : q2027347_ennreal :=
  match n with
  | O => q2027347_ennreal_zero
  | S k =>
      q2027347_ennreal_add
        (q2027347_ennreal_partial_sum u k) (u k)
  end.

Definition q2027347_ennreal_supremum
    (values : q2027347_ennreal -> Prop)
    (bound : q2027347_ennreal) : Prop :=
  (forall value : q2027347_ennreal,
      values value -> q2027347_ennreal_le value bound) /\
  (forall upper : q2027347_ennreal,
      (forall value : q2027347_ennreal,
        values value -> q2027347_ennreal_le value upper) ->
      q2027347_ennreal_le bound upper).

Definition q2027347_ennreal_series_sum
    (u : nat -> q2027347_ennreal)
    (sum : q2027347_ennreal) : Prop :=
  q2027347_ennreal_supremum
    (fun value =>
      exists n : nat,
        q2027347_ennreal_eq value
          (q2027347_ennreal_partial_sum u n))
    sum.

Definition q2027347_ennreal_represents
    (x : q2027347_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q2027347_ennreal_eq x
      (q2027347_ennreal_finite value nonnegative).

Definition q2027347_ennreal_finite_value
    (x : q2027347_ennreal) : Prop :=
  exists value : R, q2027347_ennreal_represents x value.

Record q2027347_measure {A : Type}
    (M : q2027347_measurable_space A) : Type := {
  q2027347_measure_value :
    q2027347_set A -> q2027347_ennreal;
  q2027347_measure_extensional :
    forall E F : q2027347_set A,
      q2027347_same_set E F ->
      q2027347_ennreal_eq
        (q2027347_measure_value E)
        (q2027347_measure_value F);
  q2027347_measure_empty :
    q2027347_ennreal_eq
      (q2027347_measure_value q2027347_empty)
      q2027347_ennreal_zero;
  q2027347_measure_countable_additive :
    forall E : nat -> q2027347_set A,
      (forall n : nat, q2027347_measurable M (E n)) ->
      q2027347_pairwise_disjoint E ->
      q2027347_ennreal_series_sum
        (fun n => q2027347_measure_value (E n))
        (q2027347_measure_value (q2027347_countable_union E))
}.

Arguments q2027347_measure_value {A M} _ _.

Definition q2027347_almost_everywhere {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (P : A -> Prop) : Prop :=
  exists null_set : q2027347_set A,
    q2027347_measurable M null_set /\
    q2027347_ennreal_eq
      (q2027347_measure_value mu null_set)
      q2027347_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Definition q2027347_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q2027347_finite_partition {A : Type}
    (M : q2027347_measurable_space A)
    (k : nat) (cells : nat -> q2027347_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q2027347_measurable M (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q2027347_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q2027347_measurable_simple_real {A : Type}
    (M : q2027347_measurable_space A)
    (s : A -> R) : Prop :=
  exists (k : nat) (coefficients : nat -> R)
         (cells : nat -> q2027347_set A),
    q2027347_finite_partition M k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q2027347_strongly_measurable_real {A : Type}
    (M : q2027347_measurable_space A)
    (f : A -> R) : Prop :=
  exists approximants : nat -> A -> R,
    (forall n : nat,
      q2027347_measurable_simple_real M (approximants n)) /\
    forall x : A,
      q2027347_real_sequence_converges
        (fun n => approximants n x) (f x).

Definition q2027347_ae_strongly_measurable_real {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (f : A -> R) : Prop :=
  exists approximants : nat -> A -> R,
    (forall n : nat,
      q2027347_measurable_simple_real M (approximants n)) /\
    q2027347_almost_everywhere mu
      (fun x =>
        q2027347_real_sequence_converges
          (fun n => approximants n x) (f x)).

Record q2027347_nonnegative_real : Type := {
  q2027347_nnreal_value : R;
  q2027347_nnreal_nonnegative : 0 <= q2027347_nnreal_value
}.

Definition q2027347_ennreal_of_nonnegative
    (x : q2027347_nonnegative_real) : q2027347_ennreal :=
  q2027347_ennreal_finite
    (q2027347_nnreal_value x)
    (q2027347_nnreal_nonnegative x).

Definition q2027347_simple_lintegral_below {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (f : A -> q2027347_ennreal)
    (value : q2027347_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q2027347_nonnegative_real)
         (cells : nat -> q2027347_set A),
    q2027347_finite_partition M k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q2027347_ennreal_le
        (q2027347_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q2027347_ennreal_eq value
      (q2027347_ennreal_partial_sum
        (fun i =>
          q2027347_ennreal_mul
            (q2027347_ennreal_of_nonnegative (coefficients i))
            (q2027347_measure_value mu (cells i)))
        k).

Definition q2027347_lintegral_has_value {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (f : A -> q2027347_ennreal)
    (value : q2027347_ennreal) : Prop :=
  q2027347_ennreal_supremum
    (q2027347_simple_lintegral_below mu f) value.

Definition q2027347_absolute_ennreal
    (x : R) : q2027347_ennreal :=
  q2027347_ennreal_finite (Rabs x) (Rabs_pos x).

Definition q2027347_positive_ennreal
    (x : R) : q2027347_ennreal :=
  q2027347_ennreal_finite (Rmax x 0) (Rmax_r x 0).

Definition q2027347_negative_ennreal
    (x : R) : q2027347_ennreal :=
  q2027347_ennreal_finite (Rmax (- x) 0) (Rmax_r (- x) 0).

Definition q2027347_integrable_real {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (f : A -> R) : Prop :=
  q2027347_ae_strongly_measurable_real mu f /\
  exists value : q2027347_ennreal,
    q2027347_lintegral_has_value mu
      (fun x => q2027347_absolute_ennreal (f x)) value /\
    q2027347_ennreal_finite_value value.

Definition q2027347_bochner_integral_has_value {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (f : A -> R) (value : R) : Prop :=
  exists (positive_integral negative_integral : q2027347_ennreal)
         (positive_value negative_value : R),
    q2027347_lintegral_has_value mu
      (fun x => q2027347_positive_ennreal (f x))
      positive_integral /\
    q2027347_lintegral_has_value mu
      (fun x => q2027347_negative_ennreal (f x))
      negative_integral /\
    q2027347_ennreal_represents
      positive_integral positive_value /\
    q2027347_ennreal_represents
      negative_integral negative_value /\
    value = positive_value - negative_value.

Record q2027347_integrated_measure {A : Type}
    (M : q2027347_measurable_space A) : Type := {
  q2027347_underlying_measure : q2027347_measure M;
  q2027347_integral : (A -> R) -> R;
  q2027347_integral_of_integrable :
    forall f : A -> R,
      q2027347_integrable_real q2027347_underlying_measure f ->
      q2027347_bochner_integral_has_value
        q2027347_underlying_measure f (q2027347_integral f);
  q2027347_integral_of_nonintegrable :
    forall f : A -> R,
      ~ q2027347_integrable_real q2027347_underlying_measure f ->
      q2027347_integral f = 0
}.

Arguments q2027347_underlying_measure {A M} _.
Arguments q2027347_integral {A M} _ _.

Definition q2027347_indicator {A : Type}
    (E : q2027347_set A) (f : A -> R) : A -> R :=
  fun x =>
    if excluded_middle_informative (E x) then f x else 0.

Definition q2027347_set_integral {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_integrated_measure M)
    (E : q2027347_set A) (f : A -> R) : R :=
  q2027347_integral mu (q2027347_indicator E f).

Record q2027347_filtration {A : Type}
    (ambient : q2027347_measurable_space A) : Type := {
  q2027347_filtration_level : nat -> q2027347_measurable_space A;
  q2027347_filtration_subambient :
    forall (n : nat) (E : q2027347_set A),
      q2027347_measurable (q2027347_filtration_level n) E ->
      q2027347_measurable ambient E;
  q2027347_filtration_mono :
    forall (n m : nat) (E : q2027347_set A),
      (n <= m)%nat ->
      q2027347_measurable (q2027347_filtration_level n) E ->
      q2027347_measurable (q2027347_filtration_level m) E
}.

Arguments q2027347_filtration_level {A ambient} _ _.

Definition q2027347_sigma_finite_on {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (S : q2027347_measurable_space A) : Prop :=
  exists covering : nat -> q2027347_set A,
    (forall n : nat,
      q2027347_measurable S (covering n) /\
      q2027347_ennreal_finite_value
        (q2027347_measure_value mu (covering n))) /\
    forall x : A, exists n : nat, covering n x.

Definition q2027347_sigma_finite_filtration {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_measure M)
    (F : q2027347_filtration M) : Prop :=
  forall n : nat,
    q2027347_sigma_finite_on mu
      (q2027347_filtration_level F n).

Definition q2027347_strongly_adapted {A : Type}
    {M : q2027347_measurable_space A}
    (F : q2027347_filtration M)
    (f : nat -> A -> R) : Prop :=
  forall n : nat,
    q2027347_strongly_measurable_real
      (q2027347_filtration_level F n) (f n).

Definition q2027347_submartingale {A : Type}
    {M : q2027347_measurable_space A}
    (mu : q2027347_integrated_measure M)
    (F : q2027347_filtration M)
    (f : nat -> A -> R) : Prop :=
  q2027347_strongly_adapted F f /\
  (forall n : nat,
    q2027347_integrable_real
      (q2027347_underlying_measure mu) (f n)) /\
  forall (n m : nat) (E : q2027347_set A),
    (n <= m)%nat ->
    q2027347_measurable (q2027347_filtration_level F n) E ->
    q2027347_set_integral mu E (f n) <=
    q2027347_set_integral mu E (f m).

Inductive q2027347_enat : Type :=
| q2027347_enat_finite : nat -> q2027347_enat
| q2027347_enat_infinity : q2027347_enat.

Definition q2027347_enat_le
    (x y : q2027347_enat) : Prop :=
  match x, y with
  | q2027347_enat_finite n, q2027347_enat_finite m =>
      (n <= m)%nat
  | q2027347_enat_finite _, q2027347_enat_infinity => True
  | q2027347_enat_infinity, q2027347_enat_finite _ => False
  | q2027347_enat_infinity, q2027347_enat_infinity => True
  end.

Definition q2027347_stopping_time {A : Type}
    {M : q2027347_measurable_space A}
    (F : q2027347_filtration M)
    (tau : A -> q2027347_enat) : Prop :=
  forall n : nat,
    q2027347_measurable (q2027347_filtration_level F n)
      (fun x =>
        q2027347_enat_le (tau x)
          (q2027347_enat_finite n)).

Definition q2027347_stopping_time_le {A : Type}
    (tau pi : A -> q2027347_enat) : Prop :=
  forall x : A, q2027347_enat_le (tau x) (pi x).

Definition q2027347_bounded_stopping_time {A : Type}
    (pi : A -> q2027347_enat) : Prop :=
  exists N : nat,
    forall x : A,
      q2027347_enat_le (pi x) (q2027347_enat_finite N).

Definition q2027347_stopped_value {A : Type}
    (f : nat -> A -> R)
    (tau : A -> q2027347_enat) : A -> R :=
  fun x =>
    match tau x with
    | q2027347_enat_finite n => f n x
    | q2027347_enat_infinity => 0
    end.

Theorem MeasureTheory_submartingale_iff_expected_stoppedValue_mono :
  forall (Omega : Type)
         (M : q2027347_measurable_space Omega)
         (mu : q2027347_integrated_measure M)
         (F : q2027347_filtration M)
         (f : nat -> Omega -> R),
    q2027347_sigma_finite_filtration
      (q2027347_underlying_measure mu) F ->
    q2027347_strongly_adapted F f ->
    (forall n : nat,
      q2027347_integrable_real
        (q2027347_underlying_measure mu) (f n)) ->
    (q2027347_submartingale mu F f <->
      forall tau pi : Omega -> q2027347_enat,
        q2027347_stopping_time F tau ->
        q2027347_stopping_time F pi ->
        q2027347_stopping_time_le tau pi ->
        q2027347_bounded_stopping_time pi ->
        q2027347_integral mu (q2027347_stopped_value f tau) <=
        q2027347_integral mu (q2027347_stopped_value f pi)).
Admitted.
