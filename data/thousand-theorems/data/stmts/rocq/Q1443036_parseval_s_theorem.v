(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1443036
  (thousand-theorems__rocq__Q1443036), "Parseval's theorem": for every
  complex L2 function on a positive-period additive circle, the sum over all
  integer Fourier modes of the squared coefficient norms equals its
  normalized squared L2 norm. This file contains no proof.
*)

From Stdlib Require Import Reals ZArith.ZArith ClassicalDescription
  ClassicalEpsilon.

Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1443036_set (A : Type) : Type := A -> Prop.

Definition q1443036_empty {A : Type} : q1443036_set A :=
  fun _ => False.

Definition q1443036_complement {A : Type}
    (E : q1443036_set A) : q1443036_set A :=
  fun x => ~ E x.

Definition q1443036_intersection {A : Type}
    (E F : q1443036_set A) : q1443036_set A :=
  fun x => E x /\ F x.

Definition q1443036_countable_union {A : Type}
    (E : nat -> q1443036_set A) : q1443036_set A :=
  fun x => exists n : nat, E n x.

Definition q1443036_preimage {A B : Type}
    (f : A -> B) (E : q1443036_set B) : q1443036_set A :=
  fun x => E (f x).

Definition q1443036_same_set {A : Type}
    (E F : q1443036_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1443036_disjoint {A : Type}
    (E F : q1443036_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1443036_pairwise_disjoint {A : Type}
    (E : nat -> q1443036_set A) : Prop :=
  forall i j : nat, i <> j -> q1443036_disjoint (E i) (E j).

Fixpoint q1443036_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q1443036_partial_sum u k + u k
  end.

Definition q1443036_real_series_sum
    (u : nat -> R) (sum : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (q1443036_partial_sum u n - sum) < epsilon.

Definition q1443036_sigma_class {A : Type}
    (C : q1443036_set (q1443036_set A)) : Prop :=
  C q1443036_empty /\
  (forall E F : q1443036_set A,
      q1443036_same_set E F ->
      C E ->
      C F) /\
  (forall E : q1443036_set A,
      C E ->
      C (q1443036_complement E)) /\
  (forall E : nat -> q1443036_set A,
      (forall n : nat, C (E n)) ->
      C (q1443036_countable_union E)).

Definition q1443036_open_real_set
    (U : q1443036_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Definition q1443036_borel_set
    (E : q1443036_set R) : Prop :=
  forall C : q1443036_set (q1443036_set R),
    q1443036_sigma_class C ->
    (forall U : q1443036_set R,
        q1443036_open_real_set U ->
        C U) ->
    C E.

Record q1443036_finite_borel_measure : Type := {
  q1443036_measure : q1443036_set R -> R;
  q1443036_measure_extensional :
    forall E F : q1443036_set R,
      q1443036_same_set E F ->
      q1443036_measure E = q1443036_measure F;
  q1443036_measure_nonnegative :
    forall E : q1443036_set R,
      q1443036_borel_set E ->
      0 <= q1443036_measure E;
  q1443036_measure_empty :
    q1443036_measure q1443036_empty = 0;
  q1443036_measure_countable_additive :
    forall E : nat -> q1443036_set R,
      (forall n : nat, q1443036_borel_set (E n)) ->
      q1443036_pairwise_disjoint E ->
      q1443036_real_series_sum
        (fun n => q1443036_measure (E n))
        (q1443036_measure (q1443036_countable_union E))
}.

Definition q1443036_circle_domain
    (period : R) : q1443036_set R :=
  fun x => 0 <= x < period.

Definition q1443036_half_open_interval
    (a b : R) : q1443036_set R :=
  fun x => a <= x < b.

Definition q1443036_is_circle_lebesgue_measure
    (period : R) (mu : q1443036_finite_borel_measure) : Prop :=
  (forall E : q1443036_set R,
      q1443036_borel_set E ->
      q1443036_measure mu E =
      q1443036_measure mu
        (q1443036_intersection E
          (q1443036_circle_domain period))) /\
  (forall a b : R,
      0 <= a ->
      a <= b ->
      b <= period ->
      q1443036_measure mu
        (q1443036_half_open_interval a b) = b - a).

Definition q1443036_measurable_on
    (D : q1443036_set R) (f : R -> R) : Prop :=
  forall B : q1443036_set R,
    q1443036_borel_set B ->
    q1443036_borel_set
      (q1443036_intersection D (q1443036_preimage f B)).

Definition q1443036_finite_partition
    (D : q1443036_set R) (k : nat)
    (cells : nat -> q1443036_set R) : Prop :=
  (forall i : nat,
      (i < k)%nat ->
      q1443036_borel_set (cells i)) /\
  (forall i : nat,
      (i < k)%nat ->
      forall x : R,
        cells i x ->
        D x) /\
  (forall i j : nat,
      (i < k)%nat ->
      (j < k)%nat ->
      i <> j ->
      q1443036_disjoint (cells i) (cells j)) /\
  (forall x : R,
      D x ->
      exists i : nat,
        (i < k)%nat /\ cells i x).

Definition q1443036_simple_integral_below
    (D : q1443036_set R)
    (mu : q1443036_finite_borel_measure)
    (f : R -> R) (value : R) : Prop :=
  exists (k : nat) (coefficients : nat -> R)
         (cells : nat -> q1443036_set R),
    q1443036_finite_partition D k cells /\
    (forall i : nat,
        (i < k)%nat ->
        0 <= coefficients i) /\
    (forall (x : R) (i : nat),
        (i < k)%nat ->
        cells i x ->
        coefficients i <= f x) /\
    value =
      q1443036_partial_sum
        (fun i =>
          coefficients i * q1443036_measure mu (cells i))
        k.

Definition q1443036_least_upper_bound
    (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R,
      values value ->
      value <= bound) /\
  (forall upper : R,
      (forall value : R,
          values value ->
          value <= upper) ->
      bound <= upper).

Definition q1443036_nonnegative_integral_on
    (D : q1443036_set R)
    (mu : q1443036_finite_borel_measure)
    (f : R -> R) (value : R) : Prop :=
  q1443036_least_upper_bound
    (q1443036_simple_integral_below D mu f)
    value.

Definition q1443036_positive_part (x : R) : R :=
  Rmax x 0.

Definition q1443036_negative_part (x : R) : R :=
  Rmax (- x) 0.

Definition q1443036_has_finite_integral_on
    (D : q1443036_set R)
    (mu : q1443036_finite_borel_measure)
    (f : R -> R) (value : R) : Prop :=
  q1443036_measurable_on D f /\
  exists positive_integral negative_integral : R,
    q1443036_nonnegative_integral_on D mu
      (fun x => q1443036_positive_part (f x))
      positive_integral /\
    q1443036_nonnegative_integral_on D mu
      (fun x => q1443036_negative_part (f x))
      negative_integral /\
    value = positive_integral - negative_integral.

Definition q1443036_real_integral_on
    (D : q1443036_set R)
    (mu : q1443036_finite_borel_measure)
    (f : R -> R) : R :=
  match excluded_middle_informative
          (exists value : R,
            q1443036_has_finite_integral_on D mu f value) with
  | left _ =>
      epsilon (inhabits 0)
        (fun value : R =>
          q1443036_has_finite_integral_on D mu f value)
  | right _ => 0
  end.

Record q1443036_complex : Type := {
  q1443036_re : R;
  q1443036_im : R
}.

Definition q1443036_complex_mul
    (z w : q1443036_complex) : q1443036_complex :=
  {| q1443036_re :=
       q1443036_re z * q1443036_re w -
       q1443036_im z * q1443036_im w;
     q1443036_im :=
       q1443036_re z * q1443036_im w +
       q1443036_im z * q1443036_re w |}.

Definition q1443036_complex_scale
    (a : R) (z : q1443036_complex) : q1443036_complex :=
  {| q1443036_re := a * q1443036_re z;
     q1443036_im := a * q1443036_im z |}.

Definition q1443036_modulus_squared
    (z : q1443036_complex) : R :=
  q1443036_re z * q1443036_re z +
  q1443036_im z * q1443036_im z.

Definition q1443036_complex_integral_on
    (D : q1443036_set R)
    (mu : q1443036_finite_borel_measure)
    (f : R -> q1443036_complex) : q1443036_complex :=
  {| q1443036_re :=
       q1443036_real_integral_on D mu
         (fun x => q1443036_re (f x));
     q1443036_im :=
       q1443036_real_integral_on D mu
         (fun x => q1443036_im (f x)) |}.

Definition q1443036_square_integrable_on_circle
    (period : R) (mu : q1443036_finite_borel_measure)
    (f : R -> q1443036_complex) : Prop :=
  q1443036_measurable_on
    (q1443036_circle_domain period)
    (fun x => q1443036_re (f x)) /\
  q1443036_measurable_on
    (q1443036_circle_domain period)
    (fun x => q1443036_im (f x)) /\
  exists energy : R,
    q1443036_has_finite_integral_on
      (q1443036_circle_domain period) mu
      (fun x => q1443036_modulus_squared (f x))
      energy.

Definition q1443036_fourier_character
    (period : R) (index : Z) (x : R) : q1443036_complex :=
  let angle := 2 * PI * IZR index * x / period in
  {| q1443036_re := cos angle;
     q1443036_im := - sin angle |}.

Definition q1443036_fourier_coefficient
    (period : R) (mu : q1443036_finite_borel_measure)
    (f : R -> q1443036_complex)
    (index : Z) : q1443036_complex :=
  q1443036_complex_scale (1 / period)
    (q1443036_complex_integral_on
      (q1443036_circle_domain period) mu
      (fun x =>
        q1443036_complex_mul
          (q1443036_fourier_character period index x)
          (f x))).

Definition q1443036_integer_index (n : nat) : Z :=
  if Nat.even n
  then Z.of_nat (Nat.div n 2)
  else Z.opp (Z.of_nat (Nat.div n 2 + 1)).

Theorem ThousandTheorems_Q1443036_canonical_statement :
  forall (period : R)
         (mu : q1443036_finite_borel_measure)
         (f : R -> q1443036_complex),
    0 < period ->
    q1443036_is_circle_lebesgue_measure period mu ->
    q1443036_square_integrable_on_circle period mu f ->
    q1443036_real_series_sum
      (fun n =>
        q1443036_modulus_squared
          (q1443036_fourier_coefficient
            period mu f (q1443036_integer_index n)))
      ((1 / period) *
        q1443036_real_integral_on
          (q1443036_circle_domain period) mu
          (fun x => q1443036_modulus_squared (f x))).
Proof.
Admitted.
