(*
  Statement-only formalization of Thousand Theorems corpus artifact Q191693
  (thousand-theorems__rocq__Q191693), "Lebesgue's decomposition theorem":
  every s-finite measure has a measurable extended-nonnegative density plus
  a singular part with respect to any sigma-finite measure. This file
  contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q191693_set (A : Type) : Type := A -> Prop.

Definition q191693_empty {A : Type} : q191693_set A :=
  fun _ => False.

Definition q191693_full {A : Type} : q191693_set A :=
  fun _ => True.

Definition q191693_complement {A : Type}
    (E : q191693_set A) : q191693_set A :=
  fun x => ~ E x.

Definition q191693_countable_union {A : Type}
    (E : nat -> q191693_set A) : q191693_set A :=
  fun x => exists n : nat, E n x.

Definition q191693_same_set {A : Type}
    (E F : q191693_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q191693_disjoint {A : Type}
    (E F : q191693_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q191693_pairwise_disjoint {A : Type}
    (E : nat -> q191693_set A) : Prop :=
  forall i j : nat, i <> j -> q191693_disjoint (E i) (E j).

Inductive q191693_ennreal : Type :=
| q191693_ennreal_finite :
    forall value : R, 0 <= value -> q191693_ennreal
| q191693_ennreal_infinity : q191693_ennreal.

Arguments q191693_ennreal_finite value nonnegative : clear implicits.

Definition q191693_ennreal_zero : q191693_ennreal :=
  q191693_ennreal_finite 0 (Rle_refl 0).

Definition q191693_ennreal_eq
    (x y : q191693_ennreal) : Prop :=
  match x, y with
  | q191693_ennreal_finite a _,
    q191693_ennreal_finite b _ => a = b
  | q191693_ennreal_infinity,
    q191693_ennreal_infinity => True
  | _, _ => False
  end.

Definition q191693_ennreal_le
    (x y : q191693_ennreal) : Prop :=
  match x, y with
  | q191693_ennreal_finite a _,
    q191693_ennreal_finite b _ => a <= b
  | q191693_ennreal_finite _ _,
    q191693_ennreal_infinity => True
  | q191693_ennreal_infinity,
    q191693_ennreal_finite _ _ => False
  | q191693_ennreal_infinity,
    q191693_ennreal_infinity => True
  end.

Definition q191693_ennreal_add
    (x y : q191693_ennreal) : q191693_ennreal :=
  match x, y with
  | q191693_ennreal_finite a ha,
    q191693_ennreal_finite b hb =>
      q191693_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q191693_ennreal_infinity
  end.

Definition q191693_ennreal_mul
    (x y : q191693_ennreal) : q191693_ennreal :=
  match x, y with
  | q191693_ennreal_finite a ha,
    q191693_ennreal_finite b hb =>
      q191693_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q191693_ennreal_finite a _, q191693_ennreal_infinity
  | q191693_ennreal_infinity, q191693_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q191693_ennreal_zero
      else q191693_ennreal_infinity
  | q191693_ennreal_infinity, q191693_ennreal_infinity =>
      q191693_ennreal_infinity
  end.

Fixpoint q191693_ennreal_partial_sum
    (u : nat -> q191693_ennreal)
    (n : nat) : q191693_ennreal :=
  match n with
  | O => q191693_ennreal_zero
  | S k =>
      q191693_ennreal_add
        (q191693_ennreal_partial_sum u k) (u k)
  end.

Definition q191693_ennreal_supremum
    (values : q191693_ennreal -> Prop)
    (bound : q191693_ennreal) : Prop :=
  (forall value : q191693_ennreal,
      values value -> q191693_ennreal_le value bound) /\
  (forall upper : q191693_ennreal,
      (forall value : q191693_ennreal,
        values value -> q191693_ennreal_le value upper) ->
      q191693_ennreal_le bound upper).

Definition q191693_ennreal_series_sum
    (u : nat -> q191693_ennreal)
    (sum : q191693_ennreal) : Prop :=
  q191693_ennreal_supremum
    (fun value =>
      exists n : nat,
        q191693_ennreal_eq value
          (q191693_ennreal_partial_sum u n))
    sum.

Definition q191693_ennreal_finite_value
    (x : q191693_ennreal) : Prop :=
  exists (value : R) (nonnegative : 0 <= value),
    q191693_ennreal_eq x
      (q191693_ennreal_finite value nonnegative).

Record q191693_measurable_space (A : Type) : Type := {
  q191693_measurable : q191693_set A -> Prop;
  q191693_measurable_extensional :
    forall E F : q191693_set A,
      q191693_same_set E F ->
      (q191693_measurable E <-> q191693_measurable F);
  q191693_measurable_empty :
    q191693_measurable q191693_empty;
  q191693_measurable_complement :
    forall E : q191693_set A,
      q191693_measurable E ->
      q191693_measurable (q191693_complement E);
  q191693_measurable_countable_union :
    forall E : nat -> q191693_set A,
      (forall n : nat, q191693_measurable (E n)) ->
      q191693_measurable (q191693_countable_union E)
}.

Arguments q191693_measurable {A} _ _.

Record q191693_measure {A : Type}
    (m : q191693_measurable_space A) : Type := {
  q191693_measure_value : q191693_set A -> q191693_ennreal;
  q191693_measure_extensional :
    forall E F : q191693_set A,
      q191693_same_set E F ->
      q191693_ennreal_eq
        (q191693_measure_value E)
        (q191693_measure_value F);
  q191693_measure_empty :
    q191693_ennreal_eq
      (q191693_measure_value q191693_empty)
      q191693_ennreal_zero;
  q191693_measure_countable_additive :
    forall E : nat -> q191693_set A,
      (forall n : nat, q191693_measurable m (E n)) ->
      q191693_pairwise_disjoint E ->
      q191693_ennreal_series_sum
        (fun n => q191693_measure_value (E n))
        (q191693_measure_value (q191693_countable_union E))
}.

Arguments q191693_measure_value {A m} _ _.

Definition q191693_finite_measure {A : Type}
    {m : q191693_measurable_space A}
    (mu : q191693_measure m) : Prop :=
  q191693_ennreal_finite_value
    (q191693_measure_value mu q191693_full).

Definition q191693_s_finite {A : Type}
    {m : q191693_measurable_space A}
    (mu : q191693_measure m) : Prop :=
  exists components : nat -> q191693_measure m,
    (forall n : nat, q191693_finite_measure (components n)) /\
    forall E : q191693_set A,
      q191693_measurable m E ->
      q191693_ennreal_series_sum
        (fun n => q191693_measure_value (components n) E)
        (q191693_measure_value mu E).

Definition q191693_sigma_finite {A : Type}
    {m : q191693_measurable_space A}
    (mu : q191693_measure m) : Prop :=
  exists cover : nat -> q191693_set A,
    (forall n : nat, q191693_measurable m (cover n)) /\
    (forall n : nat,
      q191693_ennreal_finite_value
        (q191693_measure_value mu (cover n))) /\
    forall x : A, exists n : nat, cover n x.

Definition q191693_ennreal_below_real
    (x : q191693_ennreal) (bound : R) : Prop :=
  match x with
  | q191693_ennreal_finite value _ => value < bound
  | q191693_ennreal_infinity => False
  end.

Definition q191693_measurable_ennreal_function {A : Type}
    (m : q191693_measurable_space A)
    (f : A -> q191693_ennreal) : Prop :=
  forall bound : R,
    q191693_measurable m
      (fun x => q191693_ennreal_below_real (f x) bound).

Definition q191693_finite_partition {A : Type}
    (m : q191693_measurable_space A)
    (k : nat) (cells : nat -> q191693_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q191693_measurable m (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q191693_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Record q191693_nonnegative_real : Type := {
  q191693_nnreal_value : R;
  q191693_nnreal_nonnegative : 0 <= q191693_nnreal_value
}.

Definition q191693_ennreal_of_nonnegative
    (x : q191693_nonnegative_real) : q191693_ennreal :=
  q191693_ennreal_finite
    (q191693_nnreal_value x)
    (q191693_nnreal_nonnegative x).

Definition q191693_simple_lintegral_below {A : Type}
    {m : q191693_measurable_space A}
    (mu : q191693_measure m)
    (f : A -> q191693_ennreal)
    (value : q191693_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q191693_nonnegative_real)
         (cells : nat -> q191693_set A),
    q191693_finite_partition m k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q191693_ennreal_le
        (q191693_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q191693_ennreal_eq value
      (q191693_ennreal_partial_sum
        (fun i =>
          q191693_ennreal_mul
            (q191693_ennreal_of_nonnegative (coefficients i))
            (q191693_measure_value mu (cells i)))
        k).

Definition q191693_lintegral_has_value {A : Type}
    {m : q191693_measurable_space A}
    (mu : q191693_measure m)
    (f : A -> q191693_ennreal)
    (value : q191693_ennreal) : Prop :=
  q191693_ennreal_supremum
    (q191693_simple_lintegral_below mu f) value.

Definition q191693_indicator {A : Type}
    (E : q191693_set A)
    (f : A -> q191693_ennreal)
    (x : A) : q191693_ennreal :=
  if excluded_middle_informative (E x)
  then f x
  else q191693_ennreal_zero.

Definition q191693_set_lintegral_has_value {A : Type}
    {m : q191693_measurable_space A}
    (mu : q191693_measure m)
    (E : q191693_set A)
    (f : A -> q191693_ennreal)
    (value : q191693_ennreal) : Prop :=
  q191693_lintegral_has_value mu
    (q191693_indicator E f) value.

Definition q191693_mutually_singular {A : Type}
    {m : q191693_measurable_space A}
    (mu nu : q191693_measure m) : Prop :=
  exists E : q191693_set A,
    q191693_measurable m E /\
    q191693_ennreal_eq
      (q191693_measure_value mu (q191693_complement E))
      q191693_ennreal_zero /\
    q191693_ennreal_eq
      (q191693_measure_value nu E)
      q191693_ennreal_zero.

Definition q191693_lebesgue_decomposition {A : Type}
    {m : q191693_measurable_space A}
    (mu singular nu : q191693_measure m)
    (f : A -> q191693_ennreal) : Prop :=
  q191693_measurable_ennreal_function m f /\
  q191693_mutually_singular singular nu /\
  forall E : q191693_set A,
    q191693_measurable m E ->
    exists density_value : q191693_ennreal,
      q191693_set_lintegral_has_value
        nu E f density_value /\
      q191693_ennreal_eq
        (q191693_measure_value mu E)
        (q191693_ennreal_add
          (q191693_measure_value singular E)
          density_value).

Theorem haveLebesgueDecomposition_of_sigmaFinite :
  forall (Alpha : Type)
         (m : q191693_measurable_space Alpha)
         (mu nu : q191693_measure m),
    q191693_s_finite mu ->
    q191693_sigma_finite nu ->
    exists (singular : q191693_measure m)
           (f : Alpha -> q191693_ennreal),
      q191693_lebesgue_decomposition mu singular nu f.
Admitted.
